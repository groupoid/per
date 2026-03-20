defmodule Per.Typechecker do
  @moduledoc """
  Core typechecker for the Per language, implementing cubical type theory.
  Includes evaluation, conversion checking, and type checking.
  """
  alias Per.AST

  defmodule Env do
    @moduledoc "Typechecking environment."
    defstruct env: %{}, ctx: %{}, files: MapSet.new(), deadline: nil, defs: %{}, name_to_mod: %{}
  end

  # --- Evaluation ---

  # --- OCaml-style Helpers ---

  @doc "Extracts domain and name/codomain from a Pi type."
  def extPiG(%AST.Pi{name: name, domain: t, codomain: g}), do: {t, {name, g}}
  def extPiG(u), do: raise "Expected Pi, got: #{inspect(u)}"

  @doc "Extracts domain and name/codomain from a Sigma type."
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
  @doc "Extracts level from Universe or Dir."
  def extKan(%AST.Universe{level: n}), do: n
  def extKan(%AST.Dir{val: n}), do: n
  def extKan(v), do: raise "Expected Universe or Dir, got: #{inspect(v)}"
  @doc "Helper for Set or Kan types."
  def extSet_or_Kan(v), do: extSet(v)

  @doc "Extracts path, u0, and u1 from a PathP type."
  def extPathP(%AST.PathP{path: v, u0: u0, u1: u1}), do: {v, u0, u1}
  def extPathP(v), do: raise "Expected PathP, got: #{inspect(v)}"

  @doc "Identity value constructor."
  def idv(t, x, y), do: %AST.App{func: %AST.App{func: %AST.Id{type: t}, arg: x}, arg: y}
  @doc "Implication value constructor (non-dependent Pi)."
  def implv(a, b), do: %AST.Pi{name: "_", domain: a, codomain: fn _ -> b end}

  @doc "Maximum of two universe levels."
  def imax(u, v) do
    lu = case u do %AST.Universe{level: l} -> l; %AST.Dir{val: l} -> l; _ -> 0 end
    lv = case v do %AST.Universe{level: l} -> l; %AST.Dir{val: l} -> l; _ -> 0 end
    %AST.Universe{level: max(lu, lv)}
  end

  defp isOne(i), do: idv(%AST.Interval{}, %AST.Dir{val: 1}, i)
  

  defp faceEnv(%AST.System{map: items}, ctx), do: faceEnv(items, ctx)
  defp faceEnv({n, v}, ctx), do: faceEnv([{n, v}], ctx)
  defp faceEnv(nil, ctx), do: ctx
  defp faceEnv(alpha, ctx) do
    Enum.reduce(alpha, ctx, fn 
      {name, val}, acc ->
        Map.put(acc, name, {:local, %AST.Interval{}, %AST.Dir{val: val}})
      _, acc -> acc
    end)
  end

  defp border(xs, v, index \\ nil) do
    if index do
      inv_index = Map.new(Enum.map(index, fn {k,v} -> {v,k} end))
      %AST.System{map: Map.new(Enum.map(xs, fn alpha -> 
        # Convert bitset to map for the system representation
        face = Per.DNF.from_bits(alpha, inv_index)
        {face, upd(face, v)} 
      end))}
    else
      %AST.System{map: Map.new(Enum.map(xs, fn alpha -> {alpha, upd(alpha, v)} end))}
    end
  end

  defp partialv(t, r) do
    atoms = AST.collect_atoms(r)
    index = Map.new(Enum.with_index(atoms))
    solved = Per.DNF.solve(r, 1, index)
    %AST.PartialP{type: %AST.System{map: border(solved, t, index).map}, phi: r}
  end

  defp upd(alpha, v), do: upd_val(alpha, v)

  defp is1(v), do: match?(%AST.Dir{val: 1}, v)

  @doc "Evaluates OR formula."
  def evalOr(v1, v2) do
    Per.DNF.eval_or(v1, v2)
  end
  @doc "Evaluates AND formula."
  def evalAnd(v1, v2), do: Per.DNF.eval_and(v1, v2)
  @doc "Negates a formula."
  def negFormula(v) do
    Per.DNF.neg_formula(v)
  end

  @doc "First projection evaluator."
  def vfst(%AST.Pair{first: u}), do: u
  def vfst(%AST.Neutral{term: v, type: %AST.Sigma{domain: a, codomain: _b}}), do: %AST.Neutral{term: %AST.Fst{expr: v}, type: a}
  def vfst(v), do: %AST.Fst{expr: v}

  @doc "Second projection evaluator."
  def vsnd(%AST.Pair{second: u}), do: u
  def vsnd(%AST.Neutral{term: v, type: %AST.Sigma{domain: a, codomain: b}}), do: %AST.Neutral{term: %AST.Snd{expr: v}, type: b.(vfst(%AST.Neutral{term: v, type: %AST.Sigma{domain: a, codomain: b}}))}
  def vsnd(v), do: %AST.Snd{expr: v}

  # --- Evaluation ---

  @doc "Evaluates an expression in a given context."
  def eval(expr, ctx) do
    do_eval(expr, ctx)
  end

  defp do_eval(expr, ctx) do
    case expr do
      # --- O(1) Fast-path for already evaluated values ---
      %AST.Neutral{} -> expr
      %AST.Dir{} -> expr
      %AST.Interval{} -> expr
      %AST.Universe{} -> expr
      %AST.Pi{codomain: f} when is_function(f) -> expr
      %AST.Sigma{codomain: f} when is_function(f) -> expr
      %AST.Lam{body: f} when is_function(f) -> expr
      %AST.PLam{body: f} when is_function(f) -> expr
      %AST.System{map: ts} when is_map(ts) -> expr

      # --- Normal Evaluation ---
      %AST.Var{name: x} -> getRho(ctx, x)
      %AST.Hole{} -> expr
      %AST.Pi{name: x, domain: a, codomain: b} ->
        if is_function(b) do
           %AST.Pi{name: x, domain: eval(a, ctx), codomain: b}
        else
           t = eval(a, ctx)
           %AST.Pi{name: x, domain: t, codomain: closByVal(ctx, x, t, b)}
        end
      %AST.Sigma{name: x, domain: a, codomain: b} ->
        if is_function(b) do
           %AST.Sigma{name: x, domain: eval(a, ctx), codomain: b}
        else
           t = eval(a, ctx)
           %AST.Sigma{name: x, domain: t, codomain: closByVal(ctx, x, t, b)}
        end
      %AST.Lam{name: x, body: b} ->
        if is_function(b) do
           %AST.Lam{name: x, body: b}
        else
           domain = if Map.has_key?(expr, :domain) && expr.domain, do: eval(expr.domain, ctx), else: %AST.Hole{}
           %AST.Lam{name: x, domain: domain, body: closByVal(ctx, x, domain, b)}
        end
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
        if is_function(e) do
           %AST.PLam{name: x, body: e}
        else
           %AST.PLam{name: x, body: fn r -> eval(e, Map.put(ctx, x, {:local, %AST.Interval{}, r})) end}
        end
      %AST.AppFormula{left: e, right: x} ->
        appFormula(eval(e, ctx), eval(x, ctx))
      %AST.Interval{} -> expr
      %AST.Dir{} -> expr
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
      %AST.System{map: xs} -> evalSystem(ctx, xs)
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
        if is_function(b) do
           %AST.W{name: x, domain: eval(a, ctx), codomain: b}
        else
           t = eval(a, ctx)
           %AST.W{name: x, domain: t, codomain: closByVal(ctx, x, t, b)}
        end
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
    res = case Map.get(ctx, x) do
      {:local, t, v} ->
        if is_struct(v, AST.Var), do: %AST.Neutral{term: v, type: t}, else: v
      {:global, _t, {:value, v}} -> v
      {:global, _t, {:exp, e}} -> eval(e, ctx)
      nil ->
        case x do
          "0" -> %AST.Universe{level: 0} # Should probably be handled in lexer/parser
          "1" -> %AST.Universe{level: 1}
          _ -> %AST.Var{name: x}
        end
    end
    res
  end

  defp safe_enum(e, _label), do: e

  defp closByVal(ctx, x, t, b) do
    # x is identifier, t is domain value, b is body expression
    fn v -> eval(b, Map.put(ctx, x, {:local, t, v})) end
  end

  defp app(f, x) do
    case f do
      %AST.Lam{body: func} when is_function(func) -> func.(x)
      %AST.PLam{body: func} when is_function(func) -> func.(x)
      %AST.System{map: xs} ->
        xs_map = if is_struct(xs), do: xs.map, else: xs
        case Map.get(xs_map, %{}) do
          nil -> 
            new_map = Map.new(Enum.map(xs_map, fn {face, term} -> {face, app(term, x)} end))
            evalSystem(%{}, new_map)
          v_empty -> app(v_empty, x)
        end
      %AST.PartialP{type: t} -> app(t, x)
      %AST.AppFormula{left: v, right: r} ->
        %AST.AppFormula{left: app(v, x), right: r}

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

      _ ->
        %AST.App{func: f, arg: x}
    end
  end

  defp appFormula(v, x) do
    case v do
      %AST.HComp{phi: phi, u: u} ->
        case x do
          %AST.Dir{val: 1} ->
            if phi == %AST.Dir{val: 1} do
              app(app(u, %AST.Dir{val: 1}), %AST.Refl{expr: %AST.Dir{val: 1}})
            else
              %AST.AppFormula{left: v, right: x}
            end
          _ -> %AST.AppFormula{left: v, right: x}
        end
      %AST.Lam{body: func} when is_function(func) -> func.(x)
      %AST.PLam{body: func} when is_function(func) -> func.(x)
      %AST.PartialP{type: t} -> appFormula(t, x)
      %AST.System{map: xs} ->
        xs_map = if is_struct(xs), do: xs.map, else: xs
        new_map = Map.new(Enum.map(xs_map, fn {face, term} -> {face, appFormula(term, x)} end))
        evalSystem(%{}, new_map)
      _ ->
        case x do
          %AST.Dir{val: 0} -> 
            try do
              {_, u0, _} = extPathP(inferV(v))
              u0
            rescue _ -> %AST.AppFormula{left: v, right: x} end
          %AST.Dir{val: 1} -> 
            try do
              {_, _, u1} = extPathP(inferV(v))
              u1
            rescue _ -> %AST.AppFormula{left: v, right: x} end
          _ ->
            %AST.AppFormula{left: v, right: x}
        end
    end
  end

  defp evalField(p, v) do
    # Simplified, need to match tags if any
    %AST.Field{expr: v, name: p}
  end


  defp upd_val(%AST.System{map: m}, v), do: upd_val(m, v)
  defp upd_val(m, v) do
    if m == %{} or m == [] or m == nil do
      v
    else
      do_upd_val(m, v)
    end
  end

  defp evalSystem(ctx, %AST.System{map: m}), do: do_eval_system(ctx, m)
  defp evalSystem(ctx, m), do: do_eval_system(ctx, m)

  defp do_eval_system(ctx, xs_map) do
    if xs_map == %{} or xs_map == [] or xs_map == nil do
      %AST.System{map: %{}}
    else

    ts_list = Enum.flat_map(xs_map, fn {face_map, term} ->
      Enum.map(face_map, fn {n, d} -> Per.DNF.solve(eval(%AST.Var{name: n}, ctx), d) end)
      |> Enum.reduce([%{}], fn faces, acc -> Per.DNF.meets(acc, faces) end)
      |> Enum.map(fn beta -> {beta, upd_val(beta, eval(term, faceEnv(beta, ctx)))} end)
    end)


    case Enum.find(ts_list, fn {face, _} -> map_size(face) == 0 end) do
      {_face, val} -> val
      nil ->
        final_list = Enum.reject(ts_list, fn {alpha, _} ->
          Enum.any?(ts_list, fn {beta, _} -> alpha != beta and Map.merge(alpha, beta) == alpha end)
        end)
        %AST.System{map: Map.new(final_list)}
    end
    end
  end

  defp evalOuc(v), do: %AST.Ouc{expr: v}

  # --- Inference and Checking ---

  # --- Conversion ---

  @doc "Infers the type of a value (in empty context)."
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

  @doc "Checks if two values are convertible (equivalent)."
  def conv(v1, v2) do
    try do
      cond do
        v1 == v2 -> true
        convInd(v1, v2) -> true
        true ->
          case {v1, v2} do
            {nil, _} -> true
            {_, nil} -> true
            _ -> conv_match(v1, v2)
          end
      end
    rescue
      e ->
        false
        reraise e, __STACKTRACE__
    end
  end
  defp is_formula(v) do
    match?(%AST.Or{}, v) or match?(%AST.And{}, v) or match?(%AST.Neg{}, v) or match?(%AST.Dir{}, v) or
    match?(%AST.Var{}, v) or match?(%AST.Neutral{type: %AST.Interval{}}, v)
  end

  defp conv_match(v1, v2) do
    if is_formula(v1) and is_formula(v2) do
      Per.DNF.logic_eq(v1, v2)
    else
      case {v1, v2} do
      {%AST.Lam{body: f}, %AST.Lam{body: g}} ->
        name = "x#{System.unique_integer([:positive])}"
        x = %AST.Neutral{term: %AST.Var{name: name}, type: %AST.Hole{}}
        conv(f.(x), g.(x))

      {%AST.PLam{body: f}, %AST.PLam{body: g}} when is_function(f) and is_function(g) ->
        name = "i#{System.unique_integer([:positive])}"
        x = %AST.Neutral{term: %AST.Var{name: name}, type: %AST.Interval{}}
        v1_eval = f.(x)
        v2_eval = g.(x)
        conv(v1_eval, v2_eval)

      {%AST.And{}, _} -> 
        Per.DNF.logic_eq(v1, v2)
      {%AST.Or{}, _} -> 
        Per.DNF.logic_eq(v1, v2)
      {%AST.Neg{}, _} -> 
        Per.DNF.logic_eq(v1, v2)
      {%AST.Dir{}, _} -> 
        Per.DNF.logic_eq(v1, v2)
      {_, %AST.And{}} -> 
        Per.DNF.logic_eq(v1, v2)
      {_, %AST.Or{}} -> 
        Per.DNF.logic_eq(v1, v2)
      {_, %AST.Neg{}} -> 
        Per.DNF.logic_eq(v1, v2)
      {_, %AST.Dir{}} -> 
        Per.DNF.logic_eq(v1, v2)

      {f, %AST.PLam{body: g}} when is_function(g) ->
        x = %AST.Neutral{term: %AST.Var{name: "j#{System.unique_integer([:positive])}"}, type: %AST.Interval{}}
        conv(appFormula(f, x), g.(x))

      {%AST.PLam{body: f}, g} when is_function(f) ->
        name = "j#{System.unique_integer([:positive])}"
        x = %AST.Neutral{term: %AST.Var{name: name}, type: %AST.Interval{}}
        conv(f.(x), appFormula(g, x))

      {f, %AST.Lam{body: g, domain: dom}} ->
        x = %AST.Neutral{term: %AST.Var{name: "x#{System.unique_integer([:positive])}"}, type: dom}
        conv(app(f, x), g.(x))

      {%AST.Lam{body: f, domain: dom}, g} ->
        x = %AST.Neutral{term: %AST.Var{name: "x#{System.unique_integer([:positive])}"}, type: dom}
        conv(f.(x), app(g, x))

      {%AST.Neutral{term: t1}, %AST.Neutral{term: t2}} ->
        conv(t1, t2)
      {%AST.Neutral{term: t1}, v2} -> conv(t1, v2)
      {v1, %AST.Neutral{term: t2}} -> conv(v1, t2)

      {%AST.Universe{level: u}, %AST.Universe{level: v}} ->
        Process.get(:per_girard, false) or u == v
      {%AST.Pair{first: a, second: b}, %AST.Pair{first: c, second: d}} -> conv(a, c) && conv(b, d)


       {%Per.AST.System{map: ts1}, %Per.AST.System{map: ts2}} ->
         if Map.keys(ts1) == Map.keys(ts2) do
           Enum.all?(ts1, fn {face, v1} -> conv(v1, Map.get(ts2, face)) end)
         else
           res1 = Enum.all?(ts1, fn {face, v1} -> 
             conv(v1, upd_val(face, %AST.System{map: ts2}))
           end)
           res2 = Enum.all?(ts2, fn {face, v2} -> 
             conv(v2, upd_val(face, %AST.System{map: ts1}))
           end)
           res1 && res2
         end
        

      {%Per.AST.System{map: ts}, v} ->
        Enum.all?(ts, fn {face, v_face} -> conv(upd_val(face, v), v_face) end)
      {v, %Per.AST.System{map: ts}} ->
        Enum.all?(ts, fn {face, v_face} -> conv(upd_val(face, v), v_face) end)

      {%AST.HComp{type: t1, phi: r1, u: u1, u0: v1}, %AST.HComp{type: t2, phi: r2, u: u2, u0: v2}} ->
         conv(t1, t2) && conv(r1, r2) && conv(u1, u2) && conv(v1, v2)

      {%AST.Transp{path: p1, phi: i1}, %AST.Transp{path: p2, phi: i2}} ->
        conv(p1, p2) && conv(i1, i2)

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
      {%AST.Universe{level: u}, %AST.Universe{level: v}} ->
        Process.get(:per_girard, false) or u == v


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

      {%AST.Partial{expr: e1}, %AST.Partial{expr: e2}} -> conv(e1, e2)
      {%AST.PartialP{type: t1, phi: r1}, %AST.PartialP{type: t2, phi: r2}} ->
        conv(r1, r2) && conv(t1, t2)
      {%AST.Sub{type: t1, phi: r1, u: u1}, %AST.Sub{type: t2, phi: r2, u: u2}} ->
        conv(t1, t2) && conv(r1, r2) && conv(u1, u2)
      {%AST.Inc{type: t1, phi: r1}, %AST.Inc{type: t2, phi: r2}} ->
        conv(t1, t2) && conv(r1, r2)
      {%AST.Ouc{expr: e1}, %AST.Ouc{expr: e2}} -> conv(e1, e2)

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
  end

  @doc "Asserts that two values are convertible, raising an error if not."
  def eqNf(v1, v2) do
    if conv(v1, v2) do
      :ok
    else
      raise "Inference error: terms not convertible: #{AST.to_string(v1)} and #{AST.to_string(v2)}"
    end
  end

  defp freshDim() do
    name = "i#{System.unique_integer([:positive])}"
    {name, %AST.Var{name: name}, %AST.Var{name: name}}
  end

  # --- Cubical Operations ---

  @doc "Cubical transport operation."
  def transport(p, phi, u0) do
    # transp p phi u0
    # OCaml: let (_, _, v) = freshDim () in match appFormula p v, phi with
    v_dim = %AST.Neutral{term: %AST.Var{name: "i#{System.unique_integer([:positive])}"}, type: %AST.Interval{}}
    ev_p = appFormula(p, v_dim)
    cond do
      is1(phi) -> u0
      match?(%AST.Universe{}, ev_p) -> u0
      match?(%AST.Pi{}, ev_p) ->
        # transp (<i> Π (x : A i), B i x) φ u₀ ~> λ (x : A 1), transp (<i> B i (transFill (<j> A -j) φ x i)) φ (u₀ (transFill (<j> A -j) φ x 1))
        {dom1, _} = extPiG(appFormula(p, %AST.Dir{val: 1}))
        %AST.Lam{name: "x", domain: dom1, body: fn x ->
          # v(i) = transFill (<j> A -j) phi x i
          v = fn i -> transFill(%AST.PLam{name: "j", body: fn j ->
            {dom_neg_j, _} = extPiG(appFormula(p, negFormula(j)))
            dom_neg_j
          end}, phi, x, i) end
          
          p_cod = %AST.PLam{name: "i", body: fn i ->
            {_, {_, cod_i}} = extPiG(appFormula(p, i))
            cod_i.(v.(i))
          end}
          transport(p_cod, phi, app(u0, v.(%AST.Dir{val: 1})))
        end}

      match?(%AST.Sigma{}, ev_p) ->
        # transp (<i> Σ (x : A i), B i x) φ u₀ ~> (transp (<j> A j) φ u₀.1, transp (<i> B i (transFill (<j> A j) φ u₀.1 i)) φ u₀.2)
        a = %AST.PLam{name: "j", body: fn j ->
          {dom_j, _} = extSigG(appFormula(p, j))
          dom_j
        end}
        v1 = fn i -> transFill(a, phi, vfst(u0), i) end
        p_cod = %AST.PLam{name: "i", body: fn i ->
          {_, {_, cod_i}} = extSigG(appFormula(p, i))
          cod_i.(v1.(i))
        end}
        v2 = transport(p_cod, phi, vsnd(u0))
        %AST.Pair{first: v1.(%AST.Dir{val: 1}), second: v2}

      match?(%AST.App{func: %AST.App{func: %AST.PathP{path: _}, arg: _}, arg: _}, ev_p) ||
      match?(%AST.PathP{}, ev_p) ->
        # transp (<i> PathP (P i) (v i) (w i)) φ u₀ ~> <j> comp (λ i, P i @ j) (φ ∨ j ∨ -j) (λ (i : I), [(φ = 1) → u₀ @ j, (j = 0) → v i, (j = 1) → w i]) (u₀ @ j)
        %AST.PLam{name: "j", body: fn j ->
          uj = appFormula(u0, j)
          r_prime = evalOr(phi, evalOr(j, negFormula(j)))
          t_comp = fn i ->
            {p_i, _, _} = extPathP(appFormula(p, i))
            appFormula(p_i, j)
          end
          u_comp = %AST.Lam{name: "i", domain: %AST.Interval{}, body: fn i ->
            {_, v_i, w_i} = extPathP(appFormula(p, i))
            sys1 = border(Per.DNF.solve(phi, 1), uj)
            sys2 = border(Per.DNF.solve(j, 0), v_i)
            sys3 = border(Per.DNF.solve(j, 1), w_i)
            %AST.System{map: Map.merge(Map.merge(sys1.map, sys2.map), sys3.map)}
          end}
          comp(t_comp, r_prime, u_comp, uj)
        end}

      true ->
        %AST.App{func: %AST.Transp{path: p, phi: phi}, arg: u0}
    end
  end

  @doc "Cubical homogeneous composition operation."
  def hcomp(t, r, u, u0) do
    case {t, r} do
      {t_v, %AST.Dir{val: 1}} ->
        case t_v do
          %AST.Pi{} -> app(app(u, %AST.Dir{val: 1}), %AST.Refl{expr: %AST.Dir{val: 1}})
          %AST.Sigma{} -> app(app(u, %AST.Dir{val: 1}), %AST.Refl{expr: %AST.Dir{val: 1}})
          %AST.PathP{} -> app(app(u, %AST.Dir{val: 1}), %AST.Refl{expr: %AST.Dir{val: 1}})
          _ -> app(u, %AST.Dir{val: 1})
        end

      {_, %AST.Dir{val: 0}} -> u0

      {%AST.Pi{domain: dom, codomain: cod}, _} ->
        # λ (x : A), hcomp (B x) φ (λ (i : I), [φ → u i 1=1 x]) (u₀ x)
        %AST.Lam{name: "x", domain: dom, body: fn x ->
          hcomp(cod.(x), r, %AST.Lam{name: "i", domain: %AST.Interval{}, body: fn i ->
            border(Per.DNF.solve(r, 1), app(app(app(u, i), %AST.Refl{expr: %AST.Dir{val: 1}}), x))
          end}, app(u0, x))
        end}

      {%AST.Sigma{domain: dom, codomain: cod}, _} ->
        # (hfill A φ (λ (k : I), [(r = 1) → (u k 1=1).1]) u₀.1 1, comp (λ i, B (hfill A φ (λ (k : I), [(r = 1) → (u k 1=1).1]) u₀.1 i)) φ (λ (k : I), [(r = 1) → (u k 1=1).2]) u₀.2)
        v1_hfill = fn j -> hfill(dom, r, %AST.Lam{name: "k", domain: %AST.Interval{}, body: fn k ->
          border(Per.DNF.solve(r, 1), vfst(app(app(u, k), %AST.Refl{expr: %AST.Dir{val: 1}})))
        end}, vfst(u0), j) end
        
        v1_final = v1_hfill.(%AST.Dir{val: 1})
        
        v2 = comp(fn i -> cod.(v1_hfill.(i)) end, r, %AST.Lam{name: "k", domain: %AST.Interval{}, body: fn k ->
          border(Per.DNF.solve(r, 1), vsnd(app(app(u, k), %AST.Refl{expr: %AST.Dir{val: 1}})))
        end}, vsnd(u0))
        
        %AST.Pair{first: v1_final, second: v2}

      {%AST.PathP{path: t_path, u0: v, u1: w}, _} ->
        # <j> hcomp (A @ j) (λ (i : I), [(r = 1) → u i 1=1, (j = 0) → v, (j = 1) → w]) (u₀ @ j)
        %AST.PLam{name: "j", body: fn j ->
          r_prime = evalOr(r, evalOr(j, negFormula(j)))
          hcomp(appFormula(t_path, j), r_prime, %AST.Lam{name: "i", domain: %AST.Interval{}, body: fn i ->
            sys1 = border(Per.DNF.solve(r, 1), appFormula(app(app(u, i), %AST.Refl{expr: %AST.Dir{val: 1}}), j))
            sys2 = border(Per.DNF.solve(j, 0), v)
            sys3 = border(Per.DNF.solve(j, 1), w)
            %AST.System{map: Map.merge(Map.merge(sys1.map, sys2.map), sys3.map)}
          end}, appFormula(u0, j))
        end}

      _ -> %AST.HComp{type: t, phi: r, u: u, u0: u0}
    end
  end

  @doc "Cubical hfill operation."
  def hfill(t, r, u, u0, j) do
    # hcomp t ((-j) \/ r) (\ i -> [r -> u (i /\ j) 1=1, (j=0) -> u0]) u0
    hcomp(t, evalOr(negFormula(j), r), %AST.Lam{name: "i", domain: %AST.Interval{}, body: fn i ->
      sys1 = border(Per.DNF.solve(r, 1), app(app(u, evalAnd(i, j)), %AST.Refl{expr: %AST.Dir{val: 1}}))
      sys2 = border(Per.DNF.solve(j, 0), u0)
      %AST.System{map: Map.merge(sys1.map, sys2.map)}
    end}, u0)
  end

  @doc "Cubical composition operation."
  def comp(t, r, u, u0) do
    # hcomp (t 1) r (\ i -> transp (\ j -> t (i \/ j)) i (u i 1=1)) (transp (\ i -> t i) 0 u0)
    hcomp(t.(%AST.Dir{val: 1}), r, %AST.Lam{name: "i", domain: %AST.Interval{}, body: fn i ->
      u_val = app(app(u, i), %AST.Refl{expr: %AST.Dir{val: 1}})
      path = %AST.PLam{name: "j", body: fn j -> t.(evalOr(i, j)) end}
      transport(path, i, u_val)
    end}, transport(%AST.PLam{name: "i", body: fn i -> t.(i) end}, %AST.Dir{val: 0}, u0))
  end

  @doc "Cubical transFill operation."
  def transFill(p, phi, u0, j) do
    # transp (\ i -> p (i /\ j)) (phi \/ -j) u0
    transport(%AST.PLam{name: "i", body: fn i -> appFormula(p, evalAnd(i, j)) end}, evalOr(phi, negFormula(j)), u0)
  end

  # --- Type Checking and Inference ---

  @doc "Checks an expression against a type in a given context."
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

        {%AST.System{map: ts}, %AST.PartialP{type: t, phi: _phi}} ->
          Enum.each(ts, fn {face, e} ->
             check(faceEnv(face, ctx), e, t)
          end)
          :ok

        {%AST.PLam{name: x, body: b}, %AST.PathP{path: p, u0: u0, u1: u1}} ->
          v0 = eval(b, Map.put(ctx, x, {:local, %AST.Interval{}, %AST.Dir{val: 0}}))
          v1 = eval(b, Map.put(ctx, x, {:local, %AST.Interval{}, %AST.Dir{val: 1}}))
          if not conv(v0, u0) do
             raise "Path endpoint mismatch at 0: expected #{AST.to_string(u0)}, got #{AST.to_string(v0)}"
          end
          if not conv(v1, u1) do
             raise "Path endpoint mismatch at 1: expected #{AST.to_string(u1)}, got #{AST.to_string(v1)}"
          end
          {_i_name, i_var, _} = freshDim()
          check(Map.put(ctx, x, {:local, %AST.Interval{}, i_var}), b, appFormula(p, i_var))

        {%AST.Neutral{type: t_v}, t} ->
          if not conv(t_v, t) do
            raise "Type mismatch: expected #{AST.to_string(t)}, got #{AST.to_string(t_v)}"
          end
          :ok

        {%AST.PLam{body: f}, %AST.PathP{path: p, u0: u0, u1: u1}} when is_function(f) ->
          v0 = f.(%AST.Dir{val: 0})
          v1 = f.(%AST.Dir{val: 1})
          if not conv(v0, u0) do
             raise "Path endpoint mismatch at 0: expected #{AST.to_string(u0)}, got #{AST.to_string(v0)}"
          end
          if not conv(v1, u1) do
             raise "Path endpoint mismatch at 1: expected #{AST.to_string(u1)}, got #{AST.to_string(v1)}"
          end
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
          if not conv(inferred, t) do
            raise "Check error: while checking #{AST.to_string(e)} against #{AST.to_string(t)}"
          end
          :ok
      end
    rescue
      e ->
        case e do
          %RuntimeError{message: "Check error: " <> _} -> reraise e, __STACKTRACE__
          _ ->
            raise "Check error: while checking #{AST.to_string(e0)} against #{AST.to_string(t0)}: #{inspect(e)}"
        end
    end
  end

  @doc "Infers the type of an expression in a given context."
  def infer(ctx, e) do
    eval(do_infer(ctx, e), ctx)
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
        tb = infer(Map.put(ctx, x, {:local, t, %AST.Var{name: x}}), b)
        %AST.Pi{name: x, domain: a, codomain: readback(tb)}

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

          %AST.PartialP{type: t, phi: i} ->
            check(ctx, x, isOne(i))
            app(t, eval(x, ctx))

          %AST.PathP{path: p_val} ->
            check(ctx, x, %AST.Interval{})
            appFormula(p_val, eval(x, ctx))

          v ->
            raise "Expected Pi or PathP, got: #{inspect(v)}"
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


      %AST.HComp{type: t, phi: r, u: u, u0: u0} ->
        t_val = eval(t, ctx)
        r_val = eval(r, ctx)
        _ = extKan(infer(ctx, t))
        check(ctx, r, %AST.Interval{})
        check(ctx, u, implv(%AST.Interval{}, partialv(t_val, r_val)))
        check(ctx, u0, t_val)
        # Check faces match at r=1
        Enum.each(Per.DNF.solve(r_val, 1), fn alpha ->
           face_ctx = faceEnv(alpha, ctx)
           u0_v = case t_val do
             %AST.Pi{} -> app(app(eval(u, face_ctx), %AST.Dir{val: 0}), %AST.Refl{expr: %AST.Dir{val: 1}})
             %AST.Sigma{} -> app(app(eval(u, face_ctx), %AST.Dir{val: 0}), %AST.Refl{expr: %AST.Dir{val: 1}})
             %AST.PathP{} -> app(app(eval(u, face_ctx), %AST.Dir{val: 0}), %AST.Refl{expr: %AST.Dir{val: 1}})
             _ -> app(eval(u, face_ctx), %AST.Dir{val: 0})
           end
           eqNf(u0_v, eval(u0, face_ctx))
        end)
        t_val

      %AST.Transp{path: p, phi: i} ->
        check(ctx, i, %AST.Interval{})
        p_val = eval(p, ctx)
        implv(appFormula(p_val, %AST.Dir{val: 0}), appFormula(p_val, %AST.Dir{val: 1}))

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
          %AST.PathP{path: p, u0: _, u1: _} ->
            appFormula(eval(p, ctx), eval(i, ctx))
          t -> raise "Expected PathP type for formula application, got: #{inspect(t)}"
        end

      %AST.PLam{name: x, body: body} ->
        # PLam x body : Pi(I, \x -> infer body)
        t = infer(Map.put(ctx, x, {:local, %AST.Interval{}, %AST.Var{name: x}}), body)
        %AST.Pi{name: x, domain: %AST.Interval{}, codomain: readback(t)}

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
        # Infer non-dependent Sigma type. For dependent, we need more info.
        %AST.Sigma{name: "_", domain: readback(ta), codomain: readback(tb)}

      %AST.System{map: ts} ->
        # checkOverlapping(ctx, ts)
        %AST.PartialP{type: %AST.System{map: Map.new(Enum.map(safe_enum(ts, "do_infer_Sys"), fn {face, term} -> {face, eval(infer(ctx, term), ctx)} end))}, phi: eval_system_formula(ts)}

      %AST.Sub{type: a, phi: i, u: u} ->
        _ = extSet(infer(ctx, a))
        check(ctx, i, %AST.Interval{})
        check(ctx, u, partialv(eval(a, ctx), eval(i, ctx)))
        %AST.Universe{level: extSet(infer(ctx, a))}

      %AST.Inc{type: t, phi: r} ->
        _ = extSet_or_Kan(infer(ctx, t))
        check(ctx, r, %AST.Interval{})
        %AST.Sub{type: eval(t, ctx), phi: eval(r, ctx), u: %AST.Hole{}} # Simplified

      %AST.Ouc{expr: e} ->
        case infer(ctx, e) do
          %AST.Sub{type: t} -> t
          _ -> raise "Expected Sub type for Ouc, got: #{inspect(infer(ctx, e))}"
        end

      %AST.Partial{expr: e} ->
        n = extSet(infer(ctx, e))
        implv(%AST.Interval{}, %AST.Universe{level: n})

      %AST.PartialP{type: t, phi: r0} ->
        check(ctx, r0, %AST.Interval{})
        case infer(ctx, t) do
          %AST.PartialP{type: ts, phi: r} ->
             eqNf(r, eval(r0, ctx))
             inferV(inferV(ts))
          _ -> raise "Expected partial function into universe"
        end

      _ -> raise "Inference not implemented for: #{inspect(e)}"
    end
  end

  defp eval_system_formula(ts) do
    Per.DNF.getFormulaV(ts)
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

  @doc "Normalizes a term by evaluating it and then reading it back."
  def normalize(env, term) do
    val = eval(term, env.ctx)
    readback(val)
  end

  @doc "Converts a value back to an AST term (readback/reify)."
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
        %AST.System{map: Map.new(Enum.map(xs, fn {face, term} -> {face, readback(term)} end))}
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

  defp do_upd_val(face, v) do
    case v do
      %AST.Var{name: n} -> 
        key_neutral = %AST.Neutral{term: v, type: %AST.Interval{}}
        cond do
          Map.has_key?(face, v) -> %AST.Dir{val: Map.get(face, v)}
          Map.has_key?(face, key_neutral) -> %AST.Dir{val: Map.get(face, key_neutral)}
          Map.has_key?(face, n) -> %AST.Dir{val: Map.get(face, n)}
          true -> v
        end
      %AST.Neutral{term: t = %AST.Var{name: n}, type: %AST.Interval{}} ->
        cond do
          Map.has_key?(face, v) -> %AST.Dir{val: Map.get(face, v)}
          Map.has_key?(face, t) -> %AST.Dir{val: Map.get(face, t)}
          Map.has_key?(face, n) -> %AST.Dir{val: Map.get(face, n)}
          true -> v
        end
      %AST.Neutral{term: t, type: ty} ->
        new_t = do_upd_val(face, t)
        new_ty = do_upd_val(face, ty)
        if new_t === t and new_ty === ty, do: v, else: %AST.Neutral{term: new_t, type: new_ty}
      %AST.Pi{name: x, domain: a, codomain: b} ->
        new_a = do_upd_val(face, a)
        if new_a === a, do: v, else: %AST.Pi{name: x, domain: new_a, codomain: b}
      %AST.Sigma{name: x, domain: a, codomain: b} ->
        new_a = do_upd_val(face, a)
        if new_a === a, do: v, else: %AST.Sigma{name: x, domain: new_a, codomain: b}
      %AST.Lam{name: x, domain: d, body: b} ->
        if is_function(b) do
           %AST.Lam{name: x, domain: do_upd_val(face, d), body: fn r -> do_upd_val(face, b.(r)) end}
        else
           %AST.Lam{name: x, domain: do_upd_val(face, d), body: do_upd_val(face, b)}
        end
      %AST.PLam{name: x, body: b} ->
        if is_function(b) do
           %AST.PLam{name: x, body: fn r -> do_upd_val(face, b.(r)) end}
        else
           %AST.PLam{name: x, body: do_upd_val(face, b)}
        end
      %AST.App{func: f, arg: x} ->
        new_f = do_upd_val(face, f)
        new_x = do_upd_val(face, x)
        if new_f === f and new_x === x, do: v, else: app(new_f, new_x)
      %AST.AppFormula{left: f, right: x} ->
        new_f = do_upd_val(face, f)
        new_x = do_upd_val(face, x)
        if new_f === f and new_x === x, do: v, else: appFormula(new_f, new_x)
      %AST.Pair{first: e1, second: e2, tag: r} ->
        new_e1 = do_upd_val(face, e1)
        new_e2 = do_upd_val(face, e2)
        if new_e1 === e1 and new_e2 === e2, do: v, else: %AST.Pair{first: new_e1, second: new_e2, tag: r}
      %AST.PathP{path: p, u0: u0, u1: u1} ->
        new_p = do_upd_val(face, p)
        new_u0 = if(u0, do: do_upd_val(face, u0))
        new_u1 = if(u1, do: do_upd_val(face, u1))
        if new_p === p and new_u0 === u0 and new_u1 === u1, do: v, else: %AST.PathP{path: new_p, u0: new_u0, u1: new_u1}
      %AST.HComp{type: t, phi: r, u: u, u0: u0} ->
        new_t = do_upd_val(face, t)
        new_r = do_upd_val(face, r)
        new_u = do_upd_val(face, u)
        new_u0 = do_upd_val(face, u0)
        if new_t === t and new_r === r and new_u === u and new_u0 === u0, do: v, else: hcomp(new_t, new_r, new_u, new_u0)
      %AST.Transp{path: p, phi: i} ->
        new_p = do_upd_val(face, p)
        new_i = do_upd_val(face, i)
        if new_p === p and new_i === i, do: v, else: %AST.Transp{path: new_p, phi: new_i}
      %AST.System{map: ts} ->
        # 1. Normalize ts to a map
        ts_map = if is_map(ts) and not is_struct(ts), do: ts, else: (if is_struct(ts, AST.System), do: ts.map, else: Map.new(ts))
        
        face_keys = Map.keys(face)
        # 2. Compatibility check and update terms
        {res_list, all_same} = Enum.reduce(ts_map, {[], true}, fn {alpha, term}, {acc, same} ->
          incompatible = Enum.any?(face, fn {k, v} ->
            av = Map.get(alpha, k)
            av != nil and av != v
          end)
          
          if incompatible do
            {acc, false}
          else
            new_alpha = Map.drop(alpha, face_keys)
            new_term = do_upd_val(face, term)
            {[{new_alpha, new_term} | acc], same and (new_alpha === alpha and new_term === term)}
          end
        end)

        if all_same and length(res_list) == map_size(ts_map) do
          v
        else
          # 3. Prune redundant faces (O(N^2) but necessary to prevent explosion)
          final_list = Enum.reject(res_list, fn {alpha, _} ->
            Enum.any?(res_list, fn {beta, _} -> alpha != beta and Map.merge(alpha, beta) == alpha end)
          end)
          %AST.System{map: Map.new(final_list)}
        end
      %AST.And{left: x, right: y} ->
        new_x = do_upd_val(face, x)
        new_y = do_upd_val(face, y)
        if new_x === x and new_y === y, do: v, else: evalAnd(new_x, new_y)
      %AST.Or{left: x, right: y} ->
        new_x = do_upd_val(face, x)
        new_y = do_upd_val(face, y)
        if new_x === x and new_y === y, do: v, else: evalOr(new_x, new_y)
      %AST.Neg{expr: e} ->
        new_e = do_upd_val(face, e)
        if new_e === e, do: v, else: negFormula(new_e)
      %AST.Dir{} -> v
      %AST.Universe{} -> v
      %AST.Interval{} -> v
      _ -> v
    end
  end

  @doc "Checks all declarations in a module."
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
# Placeholder for next chunk
