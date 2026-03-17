defmodule Per.Desugar do
  alias Per.AST

  def desugar(%AST.Module{declarations: decls} = m, env \\ %Per.Typechecker.Env{}) do
    %AST.Module{
      m
      | declarations: Enum.map(decls, fn d -> desugar_decl(d, env) end)
    }
  end

  def desugar_decl(decl, env \\ %Per.Typechecker.Env{})

  def desugar_decl(
        %AST.DeclValue{name: name, type: type, expr: expr},
        env
      ) do
    %AST.DeclValue{
      name: name,
      type: desugar_expression(type, env, name),
      expr: desugar_expression(expr, env, name)
    }
  end

  def desugar_decl(%AST.DeclTypeSignature{name: name, type: ty}, env) do
    %AST.DeclTypeSignature{name: name, type: desugar_expression(ty, env, name)}
  end

  def desugar_decl(decl, _env), do: decl

  def desugar_expression(expr, env \\ %{}, func_name \\ nil) do
    case expr do
      %AST.Lam{name: n, domain: a, body: b} ->
        %AST.Lam{
          name: n,
          domain: desugar_expression(a, env, func_name),
          body: desugar_expression(b, env, func_name)
        }

      %AST.Pi{name: n, domain: a, codomain: b} ->
        %AST.Pi{
          name: n,
          domain: desugar_expression(a, env, func_name),
          codomain: desugar_expression(b, env, func_name)
        }

      %AST.Sigma{name: n, domain: a, codomain: b} ->
        %AST.Sigma{
          name: n,
          domain: desugar_expression(a, env, func_name),
          codomain: desugar_expression(b, env, func_name)
        }

      %AST.W{name: n, domain: a, codomain: b} ->
        %AST.W{
          name: n,
          domain: desugar_expression(a, env, func_name),
          codomain: desugar_expression(b, env, func_name)
        }

      %AST.App{func: f, arg: arg} ->
        %AST.App{
          func: desugar_expression(f, env, func_name),
          arg: desugar_expression(arg, env, func_name)
        }

      %AST.Pair{first: f, second: s, tag: t} ->
        %AST.Pair{
          first: desugar_expression(f, env, func_name),
          second: desugar_expression(s, env, func_name),
          tag: t
        }

      %AST.Fst{expr: e} ->
        %AST.Fst{expr: desugar_expression(e, env, func_name)}

      %AST.Snd{expr: e} ->
        %AST.Snd{expr: desugar_expression(e, env, func_name)}

      %AST.Field{expr: e, name: n} ->
        %AST.Field{expr: desugar_expression(e, env, func_name), name: n}

      %AST.AppFormula{left: l, right: r} ->
        %AST.AppFormula{
          left: desugar_expression(l, env, func_name),
          right: desugar_expression(r, env, func_name)
        }

      %AST.PLam{expr: e} ->
        %AST.PLam{expr: desugar_expression(e, env, func_name)}

      %AST.PathP{path: p} ->
        %AST.PathP{path: desugar_expression(p, env, func_name)}

      %AST.Transp{path: p, phi: phi} ->
        %AST.Transp{
          path: desugar_expression(p, env, func_name),
          phi: desugar_expression(phi, env, func_name)
        }

      %AST.HComp{type: t, phi: phi, u: u, u0: u0} ->
        %AST.HComp{
          type: desugar_expression(t, env, func_name),
          phi: desugar_expression(phi, env, func_name),
          u: desugar_expression(u, env, func_name),
          u0: desugar_expression(u0, env, func_name)
        }

      %AST.System{map: map} ->
        %AST.System{
          map: Enum.map(map, fn {face, e} -> {face, desugar_expression(e, env, func_name)} end)
        }

      %AST.And{left: l, right: r} ->
        %AST.And{
          left: desugar_expression(l, env, func_name),
          right: desugar_expression(r, env, func_name)
        }

      %AST.Or{left: l, right: r} ->
        %AST.Or{
          left: desugar_expression(l, env, func_name),
          right: desugar_expression(r, env, func_name)
        }

      %AST.Neg{expr: e} ->
        %AST.Neg{expr: desugar_expression(e, env, func_name)}

      %AST.Refl{expr: e} ->
        %AST.Refl{expr: desugar_expression(e, env, func_name)}

      %AST.Id{type: t} ->
        %AST.Id{type: desugar_expression(t, env, func_name)}

      %AST.IdJ{expr: e} ->
        %AST.IdJ{expr: desugar_expression(e, env, func_name)}

      %AST.IndEmpty{type: t} ->
        %AST.IndEmpty{type: desugar_expression(t, env, func_name)}

      %AST.IndUnit{type: t} ->
        %AST.IndUnit{type: desugar_expression(t, env, func_name)}

      %AST.IndBool{type: t} ->
        %AST.IndBool{type: desugar_expression(t, env, func_name)}

      %AST.IndW{type: t, expr1: e1, expr2: e2} ->
        %AST.IndW{
          type: desugar_expression(t, env, func_name),
          expr1: desugar_expression(e1, env, func_name),
          expr2: desugar_expression(e2, env, func_name)
        }

      %AST.Sup{first: f, second: s} ->
        %AST.Sup{
          first: desugar_expression(f, env, func_name),
          second: desugar_expression(s, env, func_name)
        }

      _ ->
        expr
    end
  end
end
