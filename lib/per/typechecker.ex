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
      _ ->
        raise "Expected Universe, got: #{inspect(v)}"
    end
  end
  def extKan(%AST.Universe{level: n}), do: n # In our simplified model, Kan and Pre are both Universe with levels
  def extSet_or_Kan(v), do: extSet(v)

  def extPathP(%AST.App{func: %AST.App{func: %AST.App{func: %AST.PathP{path: v}, arg: _}, arg: u0}, arg: u1}), do: {v, u0, u1}
  # Note: PathP in OCaml is often applied to u0, u1. Our AST might have App nodes.
  def extPathP(v), do: raise "Expected PathP, got: #{inspect(v)}"

  def idv(t, x, y), do: %AST.App{func: %AST.App{func: %AST.Id{type: t}, arg: x}, arg: y}
  def implv(a, b), do: %AST.Pi{name: "_", domain: a, codomain: fn _ -> b end}

  def imax(%AST.Universe{level: u}, %AST.Universe{level: v}), do: %AST.Universe{level: max(u, v)}
  def imax(u, v), do: raise "Expected Universes in imax, got: #{inspect(u)}, #{inspect(v)}"

  defp is0(v), do: match?(%AST.Dir{val: 0}, v) or match?(%AST.Universe{level: 0}, v)
  defp is1(v), do: match?(%AST.Dir{val: 1}, v) or match?(%AST.Universe{level: 1}, v)

  def orFormula(v1, v2) do
    cond do
      is1(v1) or is1(v2) -> %AST.Dir{val: 1}
      is0(v1) -> v2
      is0(v2) -> v1
      true -> %AST.Or{left: v1, right: v2}
    end
  end

  def andFormula(v1, v2) do
    cond do
      is0(v1) or is0(v2) -> %AST.Dir{val: 0}
      is1(v1) -> v2
      is1(v2) -> v1
      true -> %AST.And{left: v1, right: v2}
    end
  end

  def negFormula(v) do
    cond do
      is0(v) -> %AST.Dir{val: 1}
      is1(v) -> %AST.Dir{val: 0}
      match?(%AST.Neg{expr: n}, v) -> n
      true -> %AST.Neg{expr: v}
    end
  end

  def vfst(%AST.Pair{first: u}), do: u
  def vfst(v), do: %AST.Fst{expr: v}

  def vsnd(%AST.Pair{second: u}), do: u
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
      %AST.PathP{path: e} -> %AST.PathP{path: eval(e, ctx)}
      %AST.PLam{expr: e} -> %AST.PLam{expr: eval(e, ctx)}
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
          {:local, _t, v} -> v
          {:global, _val_t, {:value, v}} -> v
          {:global, _val_t, {:exp, e}} -> eval(e, ctx)
          nil -> %AST.Var{name: x}
        end
    end
  end

  defp closByVal(ctx, x, t, b) do
    # x is identifier, t is domain value, b is body expression
    fn v -> eval(b, Map.put(ctx, x, {:local, t, v})) end
  end

  defp app(f, x) do
    case f do
      # OCaml: | VLam (_, (_, f)), v -> f v
      %AST.Lam{body: func} when is_function(func) -> func.(x)

      # --- Extensions for canonicity (Not in OCaml reference) ---

      # Reduction for J: J A P d x (Refl A x) -> d
      # f = App(App(App(IdJ, motive), d), x), x = p
      %AST.App{func: %AST.App{func: %AST.App{func: %AST.IdJ{expr: _m}, arg: d}, arg: _x_val}, arg: _p_val} ->
        case x do
          %AST.Refl{} -> d
          _ -> %AST.App{func: f, arg: x}
        end

      # Reduction for IndBool: ind₂ M f t false -> f, ind₂ M f t true -> t
      # f = App(App(IndBool(motive), f_case), t_case), x = bool_val
      %AST.App{func: %AST.App{func: %AST.IndBool{type: _m}, arg: f_case}, arg: t_case} ->
        case x do
          %AST.FalseConstant{} -> f_case
          %AST.TrueConstant{} -> t_case
          _ -> %AST.App{func: f, arg: x}
        end

      # Reduction for IndUnit: ind₁ M f star -> f
      # f = App(IndUnit(motive), s_case), x = unit_val
      %AST.App{func: %AST.IndUnit{type: _m}, arg: s_case} ->
        case x do
          %AST.Star{} -> s_case
          _ -> %AST.App{func: f, arg: x}
        end

      # Reduction for IndW:
      # indᵂ A B motive alg (sup a f) -> alg a f (λ b, indᵂ A B motive alg (f b))
      # f = App(IndW(A, B, motive), alg), x = w_val
      %AST.App{func: %AST.IndW{a: a_type, b: b_type, motive: motive}, arg: alg} ->
        case x do
          # Sup is curried: App(App(Sup(A, B), b_val), f_val)
          %AST.App{func: %AST.App{func: %AST.Sup{a: _sa, b: _sb}, arg: b_val}, arg: f_val} ->
            # alg b_val f_val (λ x, indᵂ A B motive alg (f_val x))
            inner_rec = %AST.Lam{
              name: "b",
              domain: app(b_type, b_val),
              body: fn vb ->
                app(app(app(%AST.IndW{a: a_type, b: b_type, motive: motive}, alg), alg), app(f_val, vb))
              end
            }
            app(app(app(alg, b_val), f_val), inner_rec)
          _ -> %AST.App{func: f, arg: x}
        end

      # --- End of Extensions ---


      %AST.Transp{path: p, phi: phi} -> transport(p, phi, x)
      %AST.HComp{type: t, phi: r, u: u} -> hcomp(t, r, u, x)
      _ -> %AST.App{func: f, arg: x}
    end
  end

  defp appFormula(v, x) do
    case v do
      %AST.PLam{expr: func} when is_function(func) -> func.(x)
      _ -> %AST.AppFormula{left: v, right: x}
    end
  end

  defp evalField(p, v) do
    # Simplified, need to match tags if any
    %AST.Field{expr: v, name: p}
  end

  defp evalAnd(a, b), do: andFormula(a, b)
  defp evalOr(a, b), do: orFormula(a, b)

  defp evalSystem(_ctx, xs) do
    xs # Simplified
  end

  defp evalOuc(v), do: %AST.Ouc{expr: v}

  # --- Inference and Checking ---

  # --- Conversion ---

  def conv(v1, v2) do
    v1 == v2 || conv_match(v1, v2)
  end

  defp conv_match(v1, v2) do
    case {v1, v2} do
      {%AST.Universe{level: u}, %AST.Universe{level: v}} -> u == v
      {%AST.Pair{first: a, second: b}, %AST.Pair{first: c, second: d}} -> conv(a, c) && conv(b, d)
      {%AST.Pair{first: a, second: b}, v} -> conv(vfst(v), a) && conv(vsnd(v), b)
      {v, %AST.Pair{first: a, second: b}} -> conv(vfst(v), a) && conv(vsnd(v), b)

      {%AST.Pi{domain: a, codomain: f}, %AST.Pi{domain: b, codomain: g}} ->
        # OCaml: let x = Var (p, a) in conv a b && conv (f x) (g x)
        # We need a way to generate a fresh variable or use a placeholder
        x = %AST.Var{name: "x#{System.unique_integer([:positive])}"}
        conv(a, b) && conv(f.(x), g.(x))

      {%AST.Sigma{domain: a, codomain: f}, %AST.Sigma{domain: b, codomain: g}} ->
        x = %AST.Var{name: "x#{System.unique_integer([:positive])}"}
        conv(a, b) && conv(f.(x), g.(x))

      {%AST.Lam{domain: a, body: f}, %AST.Lam{domain: b, body: g}} ->
        x = %AST.Var{name: "x#{System.unique_integer([:positive])}"}
        conv(a, b) && conv(f.(x), g.(x))
# ...
      {%AST.W{domain: a, codomain: f}, %AST.W{domain: b, codomain: g}} ->
        x = %AST.Var{name: "x#{System.unique_integer([:positive])}"}
        conv(a, b) && conv(f.(x), g.(x))

      {%AST.PLam{expr: f}, %AST.PLam{expr: g}} -> conv(f, g)

      {%AST.Var{name: u}, %AST.Var{name: v}} -> u == v

      {%AST.App{func: f, arg: a}, %AST.App{func: g, arg: b}} -> conv(f, g) && conv(a, b)
      {%AST.Fst{expr: x}, %AST.Fst{expr: y}} -> conv(x, y)
      {%AST.Snd{expr: x}, %AST.Snd{expr: y}} -> conv(x, y)

      {%AST.PathP{path: a}, %AST.PathP{path: b}} -> conv(a, b)

      {%AST.Transp{path: p, phi: i}, %AST.Transp{path: q, phi: j}} -> conv(p, q) && conv(i, j)
      {%AST.HComp{type: t1, phi: r1, u: u1, u0: v1}, %AST.HComp{type: t2, phi: r2, u: u2, u0: v2}} ->
        conv(t1, t2) && conv(r1, r2) && conv(u1, u2) && conv(v1, v2)

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

      _ -> false
    end
  end

  def eqNf(v1, v2) do
    if conv(v1, v2), do: :ok, else: raise "Inference error: terms not convertible: #{AST.to_string(v1)} and #{AST.to_string(v2)}"
  end

  defp freshDim() do
    name = "i#{System.unique_integer([:positive])}"
    {name, %AST.Var{name: name}, %AST.Var{name: name}}
  end

  # --- Cubical Operations ---

  def transport(p, phi, u0) do
    {_i, _x, v} = freshDim()
    case {appFormula(p, v), phi} do
      {_, phi_val} when is1(phi_val) -> u0
      {%AST.Universe{}, _} -> u0

      # Pi case: transp (<i> Π (x : A i), B i x) φ u₀ ~> λ (x : A 1), transp (<i> B i (transFill (<j> A -j) φ x i)) φ (u₀ (transFill (<j> A -j) φ x 1))
      {%AST.Pi{domain: _a, codomain: _b}, _} ->
        # This requires more complex closure handling. 
        # For now, return neutral term.
        %AST.Transp{path: p, phi: phi}

      _ -> %AST.App{func: %AST.Transp{path: p, phi: phi}, arg: u0}
    end
  end

  def hcomp(t, r, u, u0) do
    case {t, r} do
      {_, %AST.Dir{val: 1}} ->
        # OCaml: app (app (u, vone), VRef vone)
        # Note: OCaml VRef corresponds to our Refl or similar? 
        # check.ml: | VRef v -> VApp (VApp (VId (inferV v), v), v)
        app(app(u, %AST.Dir{val: 1}), %AST.Refl{expr: %AST.Dir{val: 1}})

      {%AST.Pi{domain: dom, codomain: cod}, _} ->
        {_i, _x, _v} = freshDim()
        # Similar to OCaml: λ (x : A), hcomp (B x) φ (λ (i : I), [φ → u i 1=1 x]) (u₀ x)
        %AST.Lam{name: "x", domain: dom, body: fn x ->
          hcomp(cod.(x), r, %AST.Lam{name: "i", domain: %AST.Interval{}, body: fn i ->
            # Border logic simplified
            app(app(u, i), x)
          end}, app(u0, x))
        end}

      _ -> %AST.HComp{type: t, phi: r, u: u, u0: u0}
    end
  end

  def comp(t, r, u, u0) do
    {i, _x, _v} = freshDim()
    # OCaml comp implementation
    hcomp(t.(%AST.Dir{val: 1}), r, %AST.Lam{name: i, domain: %AST.Interval{}, body: fn _i_val ->
      u # Simplified
    end}, transport(%AST.PLam{expr: fn _j -> t.(%AST.Dir{val: 0}) end}, %AST.Dir{val: 0}, u0))
  end

  def transFill(p, phi, _u0, j) do
    %AST.Transp{path: p, phi: orFormula(phi, negFormula(j))}
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

        {e, %AST.Universe{level: u}} ->
          case infer(ctx, e) do
            %AST.Universe{level: v} -> if u == v, do: :ok, else: raise "Universe level mismatch: expected #{u}, got #{v}"
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
      %AST.Var{name: x} -> lookup(ctx, x)
      %AST.Universe{level: u} -> %AST.Universe{level: u + 1}
      %AST.Pi{name: x, domain: a, codomain: b} ->
        _ = extSet(infer(ctx, a))
        t = eval(a, ctx)
        _ = extSet(infer(Map.put(ctx, x, {:local, t, %AST.Var{name: x}}), b))
        %AST.Universe{level: 0} # Simplified imax

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
        i_val = eval(i, ctx)
        implv(appFormula(p_val, %AST.Dir{val: 0}), appFormula(p_val, %AST.Dir{val: 1})) # Simplified transp type

      %AST.PathP{path: p} ->
        _ty_p = infer(ctx, p) # Interval -> U
        eval_p = eval(p, ctx)
        %AST.Pi{name: "u0", domain: appFormula(eval_p, %AST.Dir{val: 0}), codomain: fn u0 ->
          %AST.Pi{name: "u1", domain: appFormula(eval_p, %AST.Dir{val: 1}), codomain: fn _u1 ->
            %AST.Universe{level: 0} # Path type is in U
          end}
        end}

      %AST.AppFormula{left: e, right: i} ->
        case infer(ctx, e) do
          %AST.App{func: %AST.App{func: %AST.PathP{path: p}, arg: _u0}, arg: _u1} ->
            appFormula(p, eval(i, ctx))
          _ -> raise "Expected PathP application, got: #{inspect(e)}"
        end

      %AST.PLam{expr: body} ->
        # Highly simplified. In OCaml model, this involves fresh dimensions.
        %AST.App{func: %AST.App{func: %AST.PathP{path: %AST.PLam{expr: body}}, arg: %AST.Hole{}}, arg: %AST.Hole{}}

      %AST.Interval{} -> %AST.Universe{level: 0} # Interval is like a type

      %AST.Dir{} -> %AST.Interval{}

      %AST.Id{type: a} ->
        _ = extSet(infer(ctx, a))
        eval_a = eval(a, ctx)
        implv(eval_a, implv(eval_a, %AST.Universe{level: 0}))

      %AST.Refl{expr: e} ->
        t = infer(ctx, e)
        # Id t e e
        app(app(%AST.Id{type: t}, eval(e, ctx)), eval(e, ctx))

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
                app(c, app(app(%AST.Sup{a: x, b: f}, x), f))
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
    eval(term, env.ctx)
  end

  def check_module(%AST.Module{declarations: decls}, env) do
    Enum.reduce_while(decls, :ok, fn
      %AST.DeclValue{name: _name, expr: expr}, _acc ->
        try do
          # In OCaml checkDecl calls infer then check or vice versa.
          # Here we just infer to ensure it's well-typed.
          _ty = infer(env.ctx, expr)
          {:cont, :ok}
        rescue
          e -> {:halt, {:error, e}}
        end
      _, acc -> {:cont, acc}
    end)
  end
end
