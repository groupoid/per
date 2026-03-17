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
    no_warn = {:attribute, 1, :compile, :nowarn_unused_vars}
    
    # Add dummy function to prevent undefined_function errors for catch-all
    dummy_fun = {:function, 1, :not_implemented_in_codegen, 1, [
      {:clause, 1, [{:var, 1, :_}], [], [{:atom, 1, :skipped}]}
    ]}

    forms = [module_attr, export_all, no_warn, dummy_fun] ++ functions ++ [{:eof, 1}]
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
    if MapSet.member?(local_env, name) do
      # Sanitize variable name: must start with Uppercase ASCII
      # If first char is Unicode, prefix with 'X'
      sanitized = 
        if String.match?(String.at(name, 0), ~r/[a-zA-Z_]/) do
          String.capitalize(name)
        else
          "V_" <> (Integer.to_string(String.to_charlist(name) |> hd(), 16))
        end
      {:var, 1, String.to_atom(sanitized)}
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

  defp generate_expr(%AST.Sup{a: f, b: s}, local_env, env, mod) do
    {:tuple, 1, [{:atom, 1, :sup}, generate_expr(f, local_env, env, mod), generate_expr(s, local_env, env, mod)]}
  end

  defp generate_expr(_, _, _, _), do: {:atom, 1, :not_implemented_in_codegen}
end
