defmodule Per.Codegen do
  @moduledoc """
  Translates Per.AST into Erlang Abstract Format.
  """
  alias Per.AST

  def generate(%AST.Module{name: mod_name, declarations: decls}, env \\ %Per.Typechecker.Env{}) do
    current_mod = String.to_atom(mod_name)
    functions = Enum.flat_map(decls, &generate_decl(&1, env, current_mod))

    module_attr = {:attribute, 1, :module, current_mod}
    export_all = {:attribute, 1, :compile, :export_all}

    forms = [module_attr, export_all] ++ functions ++ [{:eof, 1}]
    {:ok, forms}
  end

  defp generate_decl(%AST.DeclValue{name: name, expr: expr}, env, mod) do
    clause = {:clause, 1, [], [], [generate_expr(expr, MapSet.new(), env, mod)]}
    [{:function, 1, String.to_atom(name), 0, [clause]}]
  end

  defp generate_decl(
         %AST.DeclForeign{name: name, erl_mod: mod, erl_func: func, type: _ty},
         _env,
         _mod
       ) do
    # For now, simple arity extraction.
    args = [{:var, 1, :X1}]

    call =
      {:call, 1, {:remote, 1, {:atom, 1, String.to_atom(mod)}, {:atom, 1, String.to_atom(func)}},
       args}

    [{:function, 1, String.to_atom(name), 1, [{:clause, 1, args, [], [call]}]}]
  end

  defp generate_decl(_, _, _), do: []

  defp generate_expr(%AST.Var{name: name}, local_env, env, current_mod) do
    # Map to Erlang variable (Capitalized) or atom if it's a global
    if MapSet.member?(local_env, name) do
      {:var, 1, String.capitalize(name) |> String.to_atom()}
    else
      # Global call: check if it's local or remote
      case Map.get(env.name_to_mod, name) do
        nil ->
          # Unknown, assume local 0-arity
          {:call, 1, {:atom, 1, String.to_atom(name)}, []}

        mod_str ->
          mod = String.to_atom(mod_str)

          if mod == current_mod do
            {:call, 1, {:atom, 1, String.to_atom(name)}, []}
          else
            {:call, 1, {:remote, 1, {:atom, 1, mod}, {:atom, 1, String.to_atom(name)}}, []}
          end
      end
    end
  end

  defp generate_expr(%AST.Universe{level: i}, _local_env, _env, _mod) do
    {:integer, 1, i}
  end

  defp generate_expr(%AST.Lam{name: x, body: body}, local_env, env, mod) do
    erl_x = {:var, 1, String.capitalize(x) |> String.to_atom()}
    new_local_env = MapSet.put(local_env, x)

    {:fun, 1,
     {:clauses, [{:clause, 1, [erl_x], [], [generate_expr(body, new_local_env, env, mod)]}]}}
  end

  defp generate_expr(%AST.App{func: f, arg: arg}, local_env, env, mod) do
    # f arg -> f(arg)
    {:call, 1, generate_expr(f, local_env, env, mod), [generate_expr(arg, local_env, env, mod)]}
  end

  defp generate_expr(%AST.Pair{first: f, second: s}, local_env, env, mod) do
    {:tuple, 1, [generate_expr(f, local_env, env, mod), generate_expr(s, local_env, env, mod)]}
  end

  defp generate_expr(%AST.Fst{expr: e}, local_env, env, mod) do
    # element(1, e)
    {:call, 1, {:atom, 1, :element}, [{:integer, 1, 1}, generate_expr(e, local_env, env, mod)]}
  end

  defp generate_expr(%AST.Snd{expr: e}, local_env, env, mod) do
    # element(2, e)
    {:call, 1, {:atom, 1, :element}, [{:integer, 1, 2}, generate_expr(e, local_env, env, mod)]}
  end

  defp generate_expr(%AST.Sup{first: f, second: s}, local_env, env, mod) do
    {:tuple, 1, [{:atom, 1, :sup}, generate_expr(f, local_env, env, mod), generate_expr(s, local_env, env, mod)]}
  end

  defp generate_expr(_, _, _, _), do: {:atom, 1, :not_implemented_in_codegen}
end
