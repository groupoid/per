defmodule Per.Typechecker do
  alias Per.AST

  defmodule Env do
    defstruct env: %{}, ctx: %{}, files: MapSet.new(), deadline: nil, defs: %{}, name_to_mod: %{}
  end

  # --- Evaluation ---

  # --- OCaml-style Helpers ---

  def extPiG(%AST.Pi{name: name, domain: t, codomain: g}), do: {t, {name, g}}
  def extPiG(u), do: raise "Expected Pi, got: #{inspect(u)}"

  def extSigG(%AST.Sigma{name: name, domain: t, codomain: g}), do: {t, {name, g}}
  def extSigG(u), do: raise "Expected Sigma, got: #{inspect(u)}"

  defp extSet(v) do
    case v do
      %AST.Universe{level: l} -> l
      %AST.Dir{val: l} -> l
      %AST.Interval{} -> 0
      _ ->
        raise "Expected Universe, got: #{inspect(v)}"
    end
  end
  def extKan(%AST.Universe{level: n}), do: n
  def extKan(%AST.Dir{val: n}), do: n
  def extKan(v), do: raise "Expected Universe or Dir, got: #{inspect(v)}"
  def extSet_or_Kan(v), do: extSet(v)

  def extPathP(%AST.PathP{path: v, u0: u0, u1: u1}), do: {v, u0, u1}
  def extPathP(v), do: raise "Expected PathP, got: #{inspect(v)}"

  def idv(t, x, y), do: %AST.App{func: %AST.App{func: %AST.Id{type: t}, arg: x}, arg: y}
  def implv(a, b), do: %AST.Pi{name: "_", domain: a, codomain: fn _ -> b end}

  def imax(u, v) do
    lu = case u do %AST.Universe{level: l} -> l; %AST.Dir{val: l} -> l; _ -> raise "Expected Universe in imax-left, got: #{inspect(u)}" end
    lv = case v do %AST.Universe{level: l} -> l; %AST.Dir{val: l} -> l; _ -> raise "Expected Universe in imax-right, got: #{inspect(v)}" end
    %AST.Universe{level: max(lu, lv)}
  end

  defp is0(v), do: match?(%AST.Dir{val: 0}, v)
  defp is1(v), do: match?(%AST.Dir{val: 1}, v)

  def evalOr(v1, v2), do: Per.DNF.eval_or(v1, v2)
  def evalAnd(v1, v2), do: Per.DNF.eval_and(v1, v2)
  def negFormula(v), do: Per.DNF.neg_formula(v)

  def vfst(%AST.Pair{first: u}), do: u
  def vfst(%AST.Neutral{term: v, type: %AST.Sigma{domain: a, codomain: _b}}), do: %AST.Neutral{term: %AST.Fst{expr: v}, type: a}
  def vfst(v), do: %AST.Fst{expr: v}

  def vsnd(%AST.Pair{second: u}), do: u
  def vsnd(%AST.Neutral{term: v, type: %AST.Sigma{domain: a, codomain: b}}), do: %AST.Neutral{term: %AST.Snd{expr: v}, type: b.(vfst(%AST.Neutral{term: v, type: %AST.Sigma{domain: a, codomain: b}}))}
  def vsnd(v), do: %AST.Snd{expr: v}

  # --- Evaluation ---

  def eval(expr, ctx) do
    case expr do
      %AST.Universe{level: l} -> %AST.Universe{level: l}
      %AST.Var{name: x} -> getRho(ctx, x)
      %AST.Hole{} -> %AST.Hole{}
      %AST.Pi{name: x, domain: a, codomain: b} ->
        t = eval(a, ctx)
        %AST.Pi{name: x, domain: t, codomain: closByVal(ctx, x, t, b)}
      %AST.Sigma{name: x, domain: a, codomain: b} ->
        t = eval(a, ctx)
        %AST.Sigma{name: x, domain: t, codomain: closByVal(ctx, x, t, b)}
      %AST.Lam{name: x, body: b} ->
        # In OCaml model, VLam has domain too. Elixir AST Lam has domain?
        # Let's check AST.Lam. It has :name, :domain, :body.
        # Wait, OCaml ELam is ELam of exp * (ident * exp).
        # Our Parser for Lam: %AST.Lam{name: x, domain: a, body: b}
        t = if Map.has_key?(expr, :domain) && expr.domain, do: eval(expr.domain, ctx), else: %AST.Hole{}
        %AST.Lam{name: x, domain: t, body: closByVal(ctx, x, t, b)}
      %AST.App{func: f, arg: x} ->
        app(eval(f, ctx), eval(x, ctx))
      %AST.Pair{first: e1, second: e2, tag: r} ->
        %AST.Pair{first: eval(e1, ctx), second: eval(e2, ctx), tag: r}
      %AST.Fst{expr: e} -> vfst(eval(e, ctx))
      %AST.Snd{expr: e} -> vsnd(eval(e, ctx))
      %AST.Field{expr: e, name: p} -> evalField(p, eval(e, ctx))
      %AST.Id{type: e} -> %AST.Id{type: eval(e, ctx)}
      %AST.Refl{expr: e} -> %AST.Refl{expr: eval(e, ctx)}
      %AST.IdJ{expr: e} -> %AST.IdJ{expr: eval(e, ctx)}
      %AST.PathP{path: e, u0: u0, u1: u1} -> %AST.PathP{path: eval(e, ctx), u0: eval(u0, ctx), u1: eval(u1, ctx)}
      %AST.PLam{name: x, body: e} ->
        %AST.PLam{name: x, body: fn r -> eval(e, Map.put(ctx, x, {:local, %AST.Interval{}, r})) end}
      %AST.AppFormula{left: e, right: x} ->
        appFormula(eval(e, ctx), eval(x, ctx))
      %AST.Interval{} -> %AST.Interval{}
      %AST.Dir{val: d} -> %AST.Dir{val: d}
      %AST.And{left: e1, right: e2} -> evalAnd(eval(e1, ctx), eval(e2, ctx))
      %AST.Or{left: e1, right: e2} -> evalOr(eval(e1, ctx), eval(e2, ctx))
      %AST.Neg{expr: e} -> negFormula(eval(e, ctx))
      %AST.Transp{path: p, phi: i} -> %AST.Transp{path: eval(p, ctx), phi: eval(i, ctx)}
      %AST.HComp{type: t, phi: r, u: u, u0: u0} ->
        hcomp(eval(t, ctx), eval(r, ctx), eval(u, ctx), eval(u0, ctx))
      %AST.Partial{expr: e} ->
        # OCaml: | EPartial e -> let (i, _, _) = freshDim () in VLam (VI, (i, fun r -> let ts = mkSystem (List.map (fun mu -> (mu, eval e (faceEnv mu ctx))) (solve r One)) in VPartialP (VSystem ts, r)))
        # For now, keep it simple or implement freshDim
        %AST.Partial{expr: eval(e, ctx)}
      %AST.PartialP{type: t, phi: r} ->
        %AST.PartialP{type: eval(t, ctx), phi: eval(r, ctx)}
      %AST.System{map: xs} -> %AST.System{map: evalSystem(ctx, xs)}
      %AST.Sub{type: a, phi: i, u: u} ->
        %AST.Sub{type: eval(a, ctx), phi: eval(i, ctx), u: eval(u, ctx)}
      %AST.Inc{type: t, phi: r} -> %AST.Inc{type: eval(t, ctx), phi: eval(r, ctx)}
      %AST.Ouc{expr: e} -> evalOuc(eval(e, ctx))
      %AST.Empty{} -> %AST.Empty{}
      %AST.IndEmpty{type: e} -> %AST.IndEmpty{type: eval(e, ctx)}
      %AST.Unit{} -> %AST.Unit{}
      %AST.Star{} -> %AST.Star{}
      %AST.IndUnit{type: e} -> %AST.IndUnit{type: eval(e, ctx)}
      %AST.Bool{} -> %AST.Bool{}
      %AST.FalseConstant{} -> %AST.FalseConstant{}
      %AST.TrueConstant{} -> %AST.TrueConstant{}
      %AST.IndBool{type: e} -> %AST.IndBool{type: eval(e, ctx)}
      %AST.W{name: x, domain: a, codomain: b} ->
        t = eval(a, ctx)
        %AST.W{name: x, domain: t, codomain: closByVal(ctx, x, t, b)}
      %AST.Sup{a: a, b: b} -> %AST.Sup{a: eval(a, ctx), b: eval(b, ctx)}
      %AST.IndW{a: a, b: b, motive: m} ->
        %AST.IndW{a: eval(a, ctx), b: eval(b, ctx), motive: eval(m, ctx)}
      _ -> expr
    end
  end

  defp lookup(ctx, x) do
    case x do
      "0" -> %AST.Universe{level: 1} # Level of 0 is 1? Or 0 is its own type?
      "1" -> %AST.Universe{level: 1}
      _ ->
        case Map.get(ctx, x) do
          {:local, t, _v} -> t
          {:global, val_t, _} -> val_t
          nil -> raise "Variable not found: #{x}"
        end
    end
  end

  defp getRho(ctx, x) do
    case x do
      "0" -> %AST.Universe{level: 0}
      "1" -> %AST.Universe{level: 1}
      _ ->
        case Map.get(ctx, x) do
          {:local, t, v} ->
            if is_struct(v, AST.Var) or is_struct(v, AST.Neutral) do
              term = if is_struct(v, AST.Neutral), do: v.term, else: v
              %AST.Neutral{term: term, type: t}
            else
              v
            end
          {:global, t, {:value, v}} ->
            if is_struct(v, AST.Var) or is_struct(v, AST.Neutral) do
              term = if is_struct(v, AST.Neutral), do: v.term, else: v
              %AST.Neutral{term: term, type: t}
            else
              v
            end
          {:global, _val_t, {:exp, e}} -> eval(e, ctx)
          nil ->
            if x == "∂", do: IO.inspect(Map.keys(ctx), label: "CTX KEYS FOR ∂")
            %AST.Var{name: x}
        end
    end
  end

  defp closByVal(ctx, x, t, b) do
    # x is identifier, t is domain value, b is body expression
    fn v -> eval(b, Map.put(ctx, x, {:local, t, v})) end
  end

  defp app(f, x) do
    case f do
      %AST.Lam{body: func} when is_function(func) -> func.(x)
      %AST.PLam{body: func} when is_function(func) -> func.(x)

      # Extensions for canonicity
      %AST.App{func: %AST.App{func: %AST.App{func: %AST.IdJ{expr: _m}, arg: d}, arg: _x_val}, arg: _p_val} ->
        case x do
          %AST.Refl{} -> d
          _ -> %AST.App{func: f, arg: x}
        end

      %AST.App{func: %AST.App{func: %AST.IndBool{type: t}, arg: f_case}, arg: t_case} ->
        case x do
          %AST.FalseConstant{} -> f_case
          %AST.TrueConstant{} -> t_case
          _ -> %AST.Neutral{term: %AST.App{func: f, arg: x}, type: app(t, x)}
        end

      %AST.App{func: %AST.IndBool{type: _t}, arg: _f_case} ->
        %AST.App{func: f, arg: x}

      %AST.IndBool{type: _t} ->
        %AST.App{func: f, arg: x}

      %AST.App{func: %AST.IndUnit{type: m}, arg: s_case} ->
        case x do
          %AST.Star{} -> s_case
          _ -> %AST.Neutral{term: %AST.App{func: f, arg: x}, type: app(m, x)}
        end

      %AST.IndUnit{type: _t} ->
        %AST.App{func: f, arg: x}

      %AST.App{func: %AST.IndW{a: a_type, b: b_type, motive: motive}, arg: alg} ->
        case x do
          %AST.App{func: %AST.App{func: %AST.Sup{a: _sa, b: _sb}, arg: b_val}, arg: f_val} ->
            inner_rec = %AST.Lam{
              name: "b",
              domain: app(b_type, b_val),
              body: fn vb -> app(app(%AST.IndW{a: a_type, b: b_type, motive: motive}, alg), app(f_val, vb)) end
            }
            app(app(app(alg, b_val), f_val), inner_rec)
          _ -> %AST.App{func: f, arg: x}
        end

      %AST.IndEmpty{type: t} ->
        %AST.Neutral{term: %AST.App{func: f, arg: x}, type: t}

      %AST.PathP{path: p, u0: nil} -> %AST.PathP{path: p, u0: x}
      %AST.PathP{path: p, u0: u0, u1: nil} -> %AST.PathP{path: p, u0: u0, u1: x}
      %AST.Transp{path: p, phi: phi} -> transport(p, phi, x)
      %AST.HComp{type: t, phi: r, u: u} -> hcomp(t, r, u, x)

      %AST.Neutral{term: term, type: %AST.Pi{domain: _a, codomain: b}} ->
         %AST.Neutral{term: %AST.App{func: term, arg: x}, type: b.(x)}

      _ -> %AST.App{func: f, arg: x}
    end
  end

  defp appFormula(v, x) do
    case v do
      %AST.PLam{body: func} when is_function(func) -> func.(x)
      %AST.Neutral{term: term, type: %AST.PathP{path: p, u0: u0, u1: u1}} ->
        case x do
          %AST.Dir{val: 0} -> u0
          %AST.Dir{val: 1} -> u1
          _ -> %AST.Neutral{term: %AST.AppFormula{left: term, right: x}, type: appFormula(p, x)}
        end
      _ -> %AST.AppFormula{left: v, right: x}
    end
  end

  defp evalField(p, v) do
    # Simplified, need to match tags if any
    %AST.Field{expr: v, name: p}
  end


  defp evalSystem(_ctx, xs) do
    xs # Simplified
  end

  defp evalOuc(v), do: %AST.Ouc{expr: v}

  # --- Inference and Checking ---

  # --- Conversion ---

  def inferV(v) do
     try do
       infer(%{}, v)
     rescue
       _ -> %AST.Hole{}
     end
  end

  def convInd(v1, v2) do
    case {inferV(v1), inferV(v2)} do
      {%AST.Unit{}, %AST.Unit{}} -> true
      {%AST.Empty{}, %AST.Empty{}} -> true
      _ -> false
    end
  end

  def conv(v1, v2) do
    if v1 == v2 or convInd(v1, v2) do
      true
    else
      case {v1, v2} do
        {nil, _} -> true
        {_, nil} -> true
        _ ->
          res = conv_match(v1, v2)
          if (match?(%AST.PathP{}, v1) or match?(%AST.HComp{}, v1)) and not res do
            IO.inspect({v1, v2}, label: "CONV FAIL CUBICAL")
          end
          res
      end
    end
  end
  defp conv_match(v1, v2) do
    case {v1, v2} do
      {%AST.Lam{body: f}, %AST.Lam{body: g}} ->
        x = %AST.Neutral{term: %AST.Var{name: "x#{System.unique_integer([:positive])}"}, type: %AST.Hole{}}
        conv(f.(x), g.(x))

      {%AST.PLam{body: f}, %AST.PLam{body: g}} when is_function(f) and is_function(g) ->
        x = %AST.Neutral{term: %AST.Var{name: "i#{System.unique_integer([:positive])}"}, type: %AST.Interval{}}
        conv(f.(x), g.(x))

      {f, %AST.PLam{body: g}} when is_function(g) ->
        x = %AST.Neutral{term: %AST.Var{name: "j#{System.unique_integer([:positive])}"}, type: %AST.Interval{}}
        conv(appFormula(f, x), g.(x))

      {%AST.PLam{body: f}, g} when is_function(f) ->
        x = %AST.Neutral{term: %AST.Var{name: "j#{System.unique_integer([:positive])}"}, type: %AST.Interval{}}
        conv(f.(x), appFormula(g, x))

      {f, %AST.Lam{body: g, domain: dom}} ->
        x = %AST.Neutral{term: %AST.Var{name: "x#{System.unique_integer([:positive])}"}, type: dom}
        conv(app(f, x), g.(x))

      {%AST.Lam{body: f, domain: dom}, g} ->
        x = %AST.Neutral{term: %AST.Var{name: "x#{System.unique_integer([:positive])}"}, type: dom}
        conv(f.(x), app(g, x))

      {%AST.Neutral{term: t1}, %AST.Neutral{term: t2}} -> conv(t1, t2)
      {%AST.Neutral{term: t1}, v2} -> conv(t1, v2)
      {v1, %AST.Neutral{term: t2}} -> conv(v1, t2)

      {%AST.Universe{level: u}, %AST.Universe{level: v}} ->
        Process.get(:per_girard, false) or u == v
      {%AST.Pair{first: a, second: b}, %AST.Pair{first: c, second: d}} -> conv(a, c) && conv(b, d)
      {%AST.Pair{first: a, second: b}, v} -> conv(vfst(v), a) && conv(vsnd(v), b)
      {v, %AST.Pair{first: a, second: b}} -> conv(vfst(v), a) && conv(vsnd(v), b)

      {%AST.Pi{domain: a, codomain: f}, %AST.Pi{domain: b, codomain: g}} ->
        x = %AST.Neutral{term: %AST.Var{name: "x#{System.unique_integer([:positive])}"}, type: a}
        conv(a, b) && conv(f.(x), g.(x))

      {%AST.Sigma{domain: a, codomain: f}, %AST.Sigma{domain: b, codomain: g}} ->
        x = %AST.Neutral{term: %AST.Var{name: "x#{System.unique_integer([:positive])}"}, type: a}
        conv(a, b) && conv(f.(x), g.(x))

      {%AST.PathP{path: p1, u0: u0, u1: u1}, %AST.PathP{path: p2, u0: v0, u1: v1}} ->
        conv(p1, p2) && conv(u0, v0) && conv(u1, v1)

      {%AST.AppFormula{left: f, right: r1}, %AST.AppFormula{left: g, right: r2}} ->
        conv(f, g) && conv(r1, r2)

      {%AST.AppFormula{left: f, right: x}, g} ->
        v_f_x = appFormula(f, x)
        v_f_x == g || case v_f_x do
          %AST.AppFormula{} -> false # No reduction, avoid recursion if structural match above failed
          _ -> conv(v_f_x, g)
        end

      {f, %AST.AppFormula{left: g, right: x}} ->
        v_g_x = appFormula(g, x)
        f == v_g_x || case v_g_x do
          %AST.AppFormula{} -> false
          _ -> conv(f, v_g_x)
        end
      {%AST.Interval{}, %AST.Interval{}} -> true
      {%AST.Dir{val: u}, %AST.Universe{level: v}} ->
        Process.get(:per_girard, false) or u == v
      {f, g} when is_struct(f, AST.Dir) or is_struct(f, AST.And) or is_struct(f, AST.Or) or is_struct(f, AST.Neg) or
                  is_struct(g, AST.Dir) or is_struct(g, AST.And) or is_struct(g, AST.Or) or is_struct(g, AST.Neg) ->
        Per.DNF.logic_eq(f, g)

      {%AST.HComp{type: t1, phi: r1, u: u1, u0: v1}, %AST.HComp{type: t2, phi: r2, u: u2, u0: v2}} ->
        conv(t1, t2) && conv(r1, r2) && conv(u1, u2) && conv(v1, v2)

      {%AST.Transp{path: p, phi: i}, %AST.Transp{path: q, phi: j}} ->
        conv(p, q) && conv(i, j)

      {%AST.App{func: f1, arg: a1}, %AST.App{func: f2, arg: a2}} ->
        conv(f1, f2) && conv(a1, a2)

      {%AST.Fst{expr: e1}, %AST.Fst{expr: e2}} -> conv(e1, e2)
      {%AST.Snd{expr: e1}, %AST.Snd{expr: e2}} -> conv(e1, e2)

      {%AST.W{domain: a, codomain: f}, %AST.W{domain: b, codomain: g}} ->
        x = %AST.Neutral{term: %AST.Var{name: "x#{System.unique_integer([:positive])}"}, type: a}
        conv(a, b) && conv(f.(x), g.(x))

      {%AST.Var{name: u}, %AST.Var{name: v}} -> u == v

      {%AST.Empty{}, %AST.Empty{}} -> true
      {%AST.Unit{}, %AST.Unit{}} -> true
      {%AST.Star{}, %AST.Star{}} -> true
      {%AST.Bool{}, %AST.Bool{}} -> true
      {%AST.FalseConstant{}, %AST.FalseConstant{}} -> true
      {%AST.TrueConstant{}, %AST.TrueConstant{}} -> true

      {%AST.Sup{a: a1, b: b1}, %AST.Sup{a: a2, b: b2}} ->
        conv(a1, a2) && conv(b1, b2)

      {%AST.IndW{a: a1, b: b1, motive: c1}, %AST.IndW{a: a2, b: b2, motive: c2}} ->
        conv(a1, a2) && conv(b1, b2) && conv(c1, c2)

      {%AST.IndBool{type: a}, %AST.IndBool{type: b}} -> conv(a, b)
      {%AST.IndUnit{type: a}, %AST.IndUnit{type: b}} -> conv(a, b)
      {%AST.IndEmpty{type: a}, %AST.IndEmpty{type: b}} -> conv(a, b)

      {v, %AST.Pair{first: a, second: b}} ->
        conv(vfst(v), a) && conv(vsnd(v), b)

      {%AST.Pair{first: a, second: b}, v} ->
        conv(a, vfst(v)) && conv(b, vsnd(v))

      {%AST.Id{type: a}, %AST.Id{type: b}} -> conv(a, b)
      {%AST.Refl{expr: a}, %AST.Refl{expr: b}} -> conv(a, b)
      {%AST.IdJ{expr: a}, %AST.IdJ{expr: b}} -> conv(a, b)

      _ -> false
    end
  end

  def eqNf(v1, v2) do
    if conv(v1, v2) do
      :ok
    else
      # IO.inspect({v1, v2}, label: "TRACE eqNf FAIL")
      raise "Inference error: terms not convertible: #{AST.to_string(v1)} and #{AST.to_string(v2)}"
    end
  end

  defp freshDim() do
    name = "i#{System.unique_integer([:positive])}"
    {name, %AST.Var{name: name}, %AST.Var{name: name}}
  end

  # --- Cubical Operations ---

  def transport(p, phi, u0) do
    v = %AST.Var{name: "v"}
    ev_p = appFormula(p, v)
    cond do
      is1(phi) -> u0
      match?(%AST.Universe{}, ev_p) -> u0
      match?(%AST.Pi{}, ev_p) ->
        # transp (Pi a b) r u = \ x -> transp (b (transp (<i> a -i) r x)) r (u (transp (<i> a -i) r x))
        # ev_p is Pi(domain=dom, codomain=cod). Note that 'cod' is a function.
        %AST.Pi{name: x, domain: dom, codomain: cod} = ev_p
        %AST.Lam{name: x, domain: dom, body: fn arg ->
          # Higher-order transport
          transport(cod.(arg), phi, app(u0, arg))
        end}
      true ->
        %AST.App{func: %AST.Transp{path: p, phi: phi}, arg: u0}
    end
  end

  def hcomp(t, r, u, u0) do
    case {t, r} do
      {_, %AST.Dir{val: 1}} ->
        app(app(u, %AST.Dir{val: 1}), %AST.Refl{expr: %AST.Dir{val: 1}})

      {%AST.Pi{domain: dom, codomain: cod}, _} ->
        # λ (x : A), hcomp (B x) φ (λ (i : I), [φ → u i 1=1 x]) (u₀ x)
        %AST.Lam{name: "x", domain: dom, body: fn x ->
          hcomp(cod.(x), r, %AST.Lam{name: "i", domain: %AST.Interval{}, body: fn i ->
            %AST.System{map: %{r => app(app(app(u, i), %AST.Refl{expr: %AST.Dir{val: 1}}), x)}}
          end}, app(u0, x))
        end}

      {%AST.Sigma{domain: dom, codomain: cod}, _} ->
        # (hfill A φ (λ (k : I), [(r = 1) → (u k 1=1).1]) u₀.1 1, comp (λ i, B (hfill A φ (λ (k : I), [(r = 1) → (u k 1=1).1]) u₀.1 i)) φ (λ (k : I), [(r = 1) → (u k 1=1).2]) u₀.2)
        v1_hfill = fn j -> hfill(dom, r, %AST.Lam{name: "k", domain: %AST.Interval{}, body: fn k ->
          %AST.System{map: %{r => vfst(app(app(u, k), %AST.Refl{expr: %AST.Dir{val: 1}}))}}
        end}, vfst(u0), j) end
        
        v1_final = v1_hfill.(%AST.Dir{val: 1})
        
        v2 = comp(fn i -> cod.(v1_hfill.(i)) end, r, %AST.Lam{name: "k", domain: %AST.Interval{}, body: fn k ->
          %AST.System{map: %{r => vsnd(app(app(u, k), %AST.Refl{expr: %AST.Dir{val: 1}}))}}
        end}, vsnd(u0))
        
        %AST.Pair{first: v1_final, second: v2}

      {%AST.PathP{path: t_path, u0: v, u1: w}, _} ->
        # <j> hcomp (A @ j) (λ (i : I), [(r = 1) → u i 1=1, (j = 0) → v, (j = 1) → w]) (u₀ @ j)
        %AST.PLam{name: "j", body: fn j ->
          r_prime = evalOr(r, evalOr(j, negFormula(j)))
          hcomp(appFormula(t_path, j), r_prime, %AST.Lam{name: "i", domain: %AST.Interval{}, body: fn i ->
            %AST.System{map: %{
              r => appFormula(app(app(u, i), %AST.Refl{expr: %AST.Dir{val: 1}}), j),
              negFormula(j) => v,
              j => w
            }}
          end}, appFormula(u0, j))
        end}

      _ -> %AST.HComp{type: t, phi: r, u: u, u0: u0}
    end
  end

  def hfill(t, r, u, u0, j) do
    # hcomp t ((-j) \/ r) (\ i -> [r -> u (i /\ j) 1=1, (j=0) -> u0]) u0
    hcomp(t, evalOr(negFormula(j), r), %AST.Lam{name: "i", domain: %AST.Interval{}, body: fn i ->
      %AST.System{map: %{
        r => app(app(u, evalAnd(i, j)), %AST.Refl{expr: %AST.Dir{val: 1}}),
        negFormula(j) => u0
      }}
    end}, u0)
  end

  def comp(t, r, u, u0) do
    # hcomp (t 1) r (\ i -> transp (\ j -> t (i \/ j)) i (u i 1=1)) (transp (\ i -> t i) 0 u0)
    hcomp(t.(%AST.Dir{val: 1}), r, %AST.Lam{name: "i", domain: %AST.Interval{}, body: fn i ->
      u_val = app(app(u, i), %AST.Refl{expr: %AST.Dir{val: 1}})
      path = %AST.PLam{name: "j", body: fn j -> t.(evalOr(i, j)) end}
      transport(path, i, u_val)
    end}, transport(%AST.PLam{name: "i", body: fn i -> t.(i) end}, %AST.Dir{val: 0}, u0))
  end

  def transFill(p, phi, u0, j) do
    # transp (\ i -> p (i /\ j)) (phi \/ -j) u0
    transport(%AST.PLam{name: "i", body: fn i -> appFormula(p, evalAnd(i, j)) end}, evalOr(phi, negFormula(j)), u0)
  end

  # --- Type Checking and Inference ---

  def check(ctx, e0, t0) do
    try do
      case {e0, t0} do
        {%AST.Lam{name: x, body: b}, %AST.Pi{domain: t, codomain: g}} ->
          vx = %AST.Var{name: x}
          ctx_prime = Map.put(ctx, x, {:local, t, vx})
          check(ctx_prime, b, g.(vx))

        {%AST.Pair{first: e1, second: e2}, %AST.Sigma{domain: t, codomain: g}} ->
          check(ctx, e1, t)
          check(ctx, e2, g.(eval(e1, ctx)))

        {%AST.PLam{name: x, body: b}, %AST.PathP{path: p, u0: u0, u1: u1}} ->
          # Check endpoints by substituting dimensions
          v0 = eval(b, Map.put(ctx, x, {:local, %AST.Interval{}, %AST.Dir{val: 0}}))
          v1 = eval(b, Map.put(ctx, x, {:local, %AST.Interval{}, %AST.Dir{val: 1}}))
          if not conv(v0, u0), do: raise "Path endpoint mismatch at 0: expected #{AST.to_string(u0)}, got #{AST.to_string(v0)}"
          if not conv(v1, u1), do: raise "Path endpoint mismatch at 1: expected #{AST.to_string(u1)}, got #{AST.to_string(v1)}"
          # Check interior
          {_i_name, i_var, _} = freshDim()
          check(Map.put(ctx, x, {:local, %AST.Interval{}, i_var}), b, appFormula(p, i_var))

        {%AST.Neutral{type: t_v}, t} ->
          if not conv(t_v, t), do: raise "Type mismatch: expected #{AST.to_string(t)}, got #{AST.to_string(t_v)}"
          :ok

        {%AST.PLam{body: f}, %AST.PathP{path: p, u0: u0, u1: u1}} when is_function(f) ->
          # check endpoints
          v0 = f.(%AST.Dir{val: 0})
          v1 = f.(%AST.Dir{val: 1})
          if not conv(v0, u0), do: raise "Path endpoint mismatch at 0: expected #{AST.to_string(u0)}, got #{AST.to_string(v0)}"
          if not conv(v1, u1), do: raise "Path endpoint mismatch at 1: expected #{AST.to_string(u1)}, got #{AST.to_string(v1)}"
          # check interior
          {i_name, i_var, _} = freshDim()
          check(Map.put(ctx, i_name, {:local, %AST.Interval{}, i_var}), f.(i_var), appFormula(p, i_var))

        {e, %AST.Universe{level: u}} ->
          case infer(ctx, e) do
            %AST.Universe{level: v} ->
              if Process.get(:per_girard, false) or u == v, do: :ok, else: raise "Universe level mismatch: expected #{u}, got #{v}"
            %AST.Dir{val: v} -> 
              if Process.get(:per_girard, false) or u == v, do: :ok, else: raise "Universe level mismatch: expected #{u}, got #{v}"
            t -> raise "Expected Universe, got: #{inspect(t)}"
          end

        {e, t} ->
          inferred = infer(ctx, e)
          eqNf(inferred, t)
      end
    rescue
      e -> raise "Check error: while checking #{AST.to_string(e0)} against #{AST.to_string(t0)}: #{inspect(e)}"
    end
  end

  def infer(ctx, e) do
    do_infer(ctx, e)
  end

  defp do_infer(ctx, e) do
    case e do
      %AST.Neutral{type: t} -> t
      %AST.Var{name: x} -> lookup(ctx, x)
      %AST.Universe{level: u} -> %AST.Universe{level: u + 1}
      %AST.Pi{name: x, domain: a, codomain: b} ->
        ta = infer(ctx, a)
        t = eval(a, ctx)
        tb = infer(Map.put(ctx, x, {:local, t, %AST.Var{name: x}}), b)
        imax(ta, tb)

      %AST.Sigma{name: x, domain: a, codomain: b} ->
        ta = infer(ctx, a)
        x_var = %AST.Var{name: x}
        tb = infer(Map.put(ctx, x, {:local, eval(a, ctx), x_var}), b)
        imax(ta, tb)

      %AST.W{name: x, domain: a, codomain: b} ->
        ta = infer(ctx, a)
        x_var = %AST.Var{name: x}
        tb = infer(Map.put(ctx, x, {:local, eval(a, ctx), x_var}), b)
        imax(ta, tb)

      %AST.Lam{name: x, domain: a, body: b} ->
        _ = extSet(infer(ctx, a))
        t = eval(a, ctx)
        _ = infer(Map.put(ctx, x, {:local, t, %AST.Var{name: x}}), b)
        %AST.Pi{name: x, domain: t, codomain: fn vx -> infer(Map.put(ctx, x, {:local, t, vx}), b) end}

      %AST.Empty{} -> %AST.Universe{level: 0}
      %AST.Unit{} -> %AST.Universe{level: 0}
      %AST.Bool{} -> %AST.Universe{level: 0}
      %AST.Star{} -> %AST.Unit{}
      %AST.FalseConstant{} -> %AST.Bool{}
      %AST.TrueConstant{} -> %AST.Bool{}

      %AST.App{func: f, arg: x} ->
        case infer(ctx, f) do
          %AST.Pi{domain: t, codomain: g} ->
            check(ctx, x, t)
            g.(eval(x, ctx))
          v -> raise "Expected Pi, got: #{inspect(v)}"
        end

      %AST.Fst{expr: e} ->
        {t, _g} = extSigG(infer(ctx, e))
        t

      %AST.Snd{expr: e} ->
        {_t, {_p, g}} = extSigG(infer(ctx, e))
        g.(vfst(eval(e, ctx)))

      %AST.IndEmpty{type: e} ->
        _ = extSet(infer(ctx, e))
        implv(%AST.Empty{}, eval(e, ctx))

      %AST.IndUnit{type: e} ->
        # OCaml: let (t', (p, g)) = extPiG (infer ctx e) in eqNf VUnit t'; ...
        {t_prime, {_p, g}} = extPiG(infer(ctx, e))
        eqNf(%AST.Unit{}, t_prime)
        _ = extSet(g.(%AST.Star{}))
        rec_unit(eval(e, ctx))

      %AST.IndBool{type: e} ->
        {t_prime, {_p, g}} = extPiG(infer(ctx, e))
        eqNf(%AST.Bool{}, t_prime)
        _ = extSet(g.(%AST.FalseConstant{}))
        rec_bool(eval(e, ctx))

      %AST.Sup{a: a, b: b} ->
        t = eval(a, ctx)
        _ = extSet(infer(ctx, a))
        {t_prime, {_p, g}} = extPiG(infer(ctx, b))
        eqNf(t, t_prime)
        # OCaml: ignore (extSet (g (Var (p, t))))
        # Note: OCaml uses Var(p, t). freshName for p is implied.
        _ = extSet(g.(%AST.Var{name: "_"}))
        infer_sup(t, eval(b, ctx))

      %AST.IndW{a: a, b: b, motive: c} ->
        # OCaml logic for IndW: inferIndW t (eval b ctx) (eval c ctx)
        t = eval(a, ctx)
        _ = extSet(infer(ctx, a))
        {t_prime, {_p, g}} = extPiG(infer(ctx, b))
        eqNf(t, t_prime)
        _ = extSet(g.(%AST.Var{name: "_"}))

        {w_prime, {_q, h}} = extPiG(infer(ctx, c))
        eqNf(wtype(t, eval(b, ctx)), w_prime)
        _ = extSet(h.(%AST.Var{name: "_"}))

        infer_ind_w(t, eval(b, ctx), eval(c, ctx))


      %AST.Transp{path: p, phi: i} ->
        _ty_p = infer(ctx, p) # Should be Interval -> U
        _ty_i = infer(ctx, i) # Should be Interval
        p_val = eval(p, ctx)
        _i_val = eval(i, ctx)
        implv(appFormula(p_val, %AST.Dir{val: 0}), appFormula(p_val, %AST.Dir{val: 1})) # Simplified transp type

      %AST.PathP{path: p, u0: nil} ->
        eval_p = eval(p, ctx)
        %AST.Pi{name: "u0", domain: appFormula(eval_p, %AST.Dir{val: 0}), codomain: fn _u0 ->
          %AST.Pi{name: "u1", domain: appFormula(eval_p, %AST.Dir{val: 1}), codomain: fn _u1 ->
            %AST.Universe{level: 0}
          end}
        end}

      %AST.PathP{path: p, u0: u0, u1: nil} ->
        eval_p = eval(p, ctx)
        _eval_u0 = eval(u0, ctx)
        %AST.Pi{name: "u1", domain: appFormula(eval_p, %AST.Dir{val: 1}), codomain: fn _u1 ->
          %AST.Universe{level: 0}
        end}

      %AST.PathP{path: _, u0: _, u1: _} -> %AST.Universe{level: 0}

      %AST.AppFormula{left: e, right: i} ->
        case infer(ctx, e) do
          %AST.PathP{path: p_val, u0: _, u1: _} ->
            appFormula(p_val, eval(i, ctx))
          t -> raise "Expected PathP type for formula application, got: #{inspect(t)}"
        end

      %AST.PLam{name: x, body: body} ->
        # PLam x body : Pi(I, \x -> infer body)
        %AST.Pi{name: x, domain: %AST.Interval{}, codomain: fn r ->
          infer(Map.put(ctx, x, {:local, %AST.Interval{}, r}), body)
        end}

      %AST.Interval{} -> %AST.Universe{level: 0} # Interval is like a type

      %AST.Dir{} -> %AST.Interval{}

      %AST.And{left: e1, right: e2} ->
        check(ctx, e1, %AST.Interval{})
        check(ctx, e2, %AST.Interval{})
        %AST.Interval{}

      %AST.Or{left: e1, right: e2} ->
        check(ctx, e1, %AST.Interval{})
        check(ctx, e2, %AST.Interval{})
        %AST.Interval{}

      %AST.Neg{expr: e} ->
        check(ctx, e, %AST.Interval{})
        %AST.Interval{}

      %AST.Id{type: a} ->
        _ = extSet(infer(ctx, a))
        eval_a = eval(a, ctx)
        implv(eval_a, implv(eval_a, %AST.Universe{level: 0}))

      %AST.Refl{expr: e} ->
        t = infer(ctx, e)
        # Id t e e
        app(app(%AST.Id{type: t}, eval(e, ctx)), eval(e, ctx))

      %AST.Pair{first: a, second: b} ->
        ta = infer(ctx, a)
        tb = infer(ctx, b)
        # Infer non-dependent Sigma type
        %AST.Sigma{domain: eval(ta, ctx), codomain: fn _ -> eval(tb, ctx) end}

      _ -> raise "Inference not implemented for: #{inspect(e)}"
    end
  end

  defp rec_unit(t) do
    implv(app(t, %AST.Star{}), %AST.Pi{name: "x", domain: %AST.Unit{}, codomain: fn vx -> app(t, vx) end})
  end

  defp rec_bool(t) do
    implv(app(t, %AST.FalseConstant{}),
      implv(app(t, %AST.TrueConstant{}),
        %AST.Pi{name: "x", domain: %AST.Bool{}, codomain: fn vx -> app(t, vx) end}))
  end

  defp infer_ind_w(a, b, c) do
    t = wtype(a, b)
    # implv (VPi (a, (freshName "x", fun x -> ...))) (VPi (t, (freshName "w", fun w -> app (c, w))))
    implv(
      %AST.Pi{
        name: "x",
        domain: a,
        codomain: fn x ->
          %AST.Pi{
            name: "f",
            domain: implv(app(b, x), t),
            codomain: fn f ->
              implv(
                %AST.Pi{
                  name: "b",
                  domain: app(b, x),
                  codomain: fn b_val -> app(c, app(f, b_val)) end
                },
                app(c, app(app(%AST.Sup{a: a, b: b}, x), f))
              )
            end
          }
        end
      },
      %AST.Pi{name: "w", domain: t, codomain: fn w -> app(c, w) end}
    )
  end

  defp infer_sup(a, b) do
    t = wtype(a, b)
    # VPi (a, (x, fun x -> implv (implv (app (b, x)) t) t))
    %AST.Pi{name: "x", domain: a, codomain: fn x ->
      implv(implv(app(b, x), t), t)
    end}
  end

  defp wtype(a, b) do
    %AST.W{name: "x", domain: a, codomain: fn x -> app(b, x) end}
  end

  def normalize(env, term) do
    val = eval(term, env.ctx)
    readback(val)
  end

  def readback(val) do
    case val do
      %AST.Universe{level: l} -> %AST.Universe{level: l}
      %AST.Pi{name: x, domain: a, codomain: f} when is_function(f) ->
        %AST.Pi{name: x, domain: readback(a), codomain: readback(f.(%AST.Var{name: x}))}
      %AST.Sigma{name: x, domain: a, codomain: f} when is_function(f) ->
        %AST.Sigma{name: x, domain: readback(a), codomain: readback(f.(%AST.Var{name: x}))}
      %AST.Lam{name: x, body: f} when is_function(f) ->
        # Type is not strictly needed for readback of Lam if we don't store it
        %AST.Lam{name: x, body: readback(f.(%AST.Var{name: x}))}
      %AST.Pair{first: a, second: b, tag: r} ->
        %AST.Pair{first: readback(a), second: readback(b), tag: r}
      %AST.Var{name: x} -> %AST.Var{name: x}
      %AST.Neutral{term: t} -> readback(t)
      %AST.App{func: f, arg: a} -> %AST.App{func: readback(f), arg: readback(a)}
      %AST.Fst{expr: e} -> %AST.Fst{expr: readback(e)}
      %AST.Snd{expr: e} -> %AST.Snd{expr: readback(e)}
      %AST.PathP{path: p, u0: u0, u1: u1} ->
        %AST.PathP{path: readback(p), u0: if(u0, do: readback(u0)), u1: if(u1, do: readback(u1))}
      %AST.PLam{name: x, body: f} when is_function(f) ->
        %AST.PLam{name: x, body: readback(f.(%AST.Var{name: x}))}
      %AST.AppFormula{left: e, right: x} ->
        %AST.AppFormula{left: readback(e), right: readback(x)}
      %AST.Interval{} -> %AST.Interval{}
      %AST.Dir{val: d} -> %AST.Dir{val: d}
      %AST.And{left: e1, right: e2} -> %AST.And{left: readback(e1), right: readback(e2)}
      %AST.Or{left: e1, right: e2} -> %AST.Or{left: readback(e1), right: readback(e2)}
      %AST.Neg{expr: e} -> %AST.Neg{expr: readback(e)}
      %AST.Transp{path: p, phi: i} -> %AST.Transp{path: readback(p), phi: readback(i)}
      %AST.HComp{type: t, phi: r, u: u, u0: u0} ->
        %AST.HComp{type: readback(t), phi: readback(r), u: readback(u), u0: readback(u0)}
      %AST.Partial{expr: e} -> %AST.Partial{expr: readback(e)}
      %AST.PartialP{type: t, phi: r} -> %AST.PartialP{type: readback(t), phi: readback(r)}
      %AST.System{map: xs} ->
        %AST.System{map: Enum.map(xs, fn {face, term} -> {face, readback(term)} end)}
      %AST.Sub{type: a, phi: i, u: u} ->
        %AST.Sub{type: readback(a), phi: readback(i), u: readback(u)}
      %AST.Inc{type: t, phi: r} -> %AST.Inc{type: readback(t), phi: readback(r)}
      %AST.Ouc{expr: e} -> %AST.Ouc{expr: readback(e)}
      %AST.Empty{} -> %AST.Empty{}
      %AST.IndEmpty{type: e} -> %AST.IndEmpty{type: readback(e)}
      %AST.Unit{} -> %AST.Unit{}
      %AST.Star{} -> %AST.Star{}
      %AST.IndUnit{type: e} -> %AST.IndUnit{type: readback(e)}
      %AST.Bool{} -> %AST.Bool{}
      %AST.FalseConstant{} -> %AST.FalseConstant{}
      %AST.TrueConstant{} -> %AST.TrueConstant{}
      %AST.IndBool{type: e} -> %AST.IndBool{type: readback(e)}
      %AST.W{name: x, domain: a, codomain: f} when is_function(f) ->
        %AST.W{name: x, domain: readback(a), codomain: readback(f.(%AST.Var{name: x}))}
      %AST.Sup{a: a, b: b} -> %AST.Sup{a: readback(a), b: readback(b)}
      %AST.IndW{a: a, b: b, motive: m} ->
        %AST.IndW{a: readback(a), b: readback(b), motive: readback(m)}
      _ -> val
    end
  end

  def check_module(%AST.Module{declarations: decls}, env) do
    # Build a lookup for types to support checking with signatures
    types = Enum.reduce(decls, %{}, fn
      %AST.DeclTypeSignature{name: name, type: ty}, acc -> Map.put(acc, name, ty)
      %AST.DeclValue{name: name, type: ty}, acc ->
        case ty do
          %AST.Hole{} -> acc
          _ -> Map.put(acc, name, ty)
        end
      _, acc -> acc
    end)

    Enum.reduce_while(decls, :ok, fn
      {:option, "girard", val}, _acc ->
        Process.put(:per_girard, val)
        {:cont, :ok}

      %AST.DeclValue{name: name, expr: expr}, _acc ->
        try do
          signature = Map.get(types, name)
          if signature do
            check(env.ctx, expr, eval(signature, env.ctx))
          else
            _ty = infer(env.ctx, expr)
          end
          {:cont, :ok}
        rescue
          e -> {:halt, {:error, e}}
        end
      _, acc -> {:cont, acc}
    end)
  end
end
