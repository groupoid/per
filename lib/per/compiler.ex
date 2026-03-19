defmodule Per.Compiler do
  @moduledoc """
  Main entry point for the Per compiler.
  """
  alias Per.{Layout, Desugar, Codegen, AST}

  def compile_module(source, opts \\ []) do
    syntax = Keyword.get(opts, :syntax, :lean)
    lexer = case syntax do
      :agda -> Per.Lexer.Agda
      _ -> Per.Lexer
    end
    parser = case syntax do
      :agda -> Per.Parser.Agda
      _ -> Per.Parser
    end

    tokens = lexer.lex(source)
    with resolved <- Layout.resolve(tokens),
         {:ok, ast, _rest} <- parser.parse(resolved) do




      initial_env = Keyword.get(opts, :env, %Per.Typechecker.Env{})
      env = resolve_imports(ast, initial_env, opts)
      env = collect_local_names(ast, env)
      desugared = Desugar.desugar(ast, env)
      final_env = populate_local_env(desugared, env)
      typecheck_res =
        if Keyword.get(opts, :typecheck, true) do
          case Per.Typechecker.check_module(desugared, final_env) do
            :ok -> :ok
            {:error, reason} -> {:error, {:type_error, reason}}
          end
        else
          :ok
        end

      if typecheck_res == :ok and Keyword.get(opts, :check_only, false) do
        {:ok, desugared.name, :check_only}
      else
        with :ok <- typecheck_res,
             {:ok, forms} <- Codegen.generate(desugared, env) do
          case :compile.forms(forms, [:return_errors, :debug_info]) do
            {:ok, mod, bin} -> {:ok, mod, bin}
            {:error, errors, warnings} -> {:error, {:erl_compile, errors, warnings}}
          end
        end
      end
    else
      err -> err
    end
  end

  defp populate_local_env(%AST.Module{name: _mod_name, declarations: decls}, env) do
    Enum.reduce(decls, env, fn
      %AST.DeclValue{} = v, acc ->
        desugared_v = Per.Desugar.desugar_decl(v, acc)
        eval_ty =
          case desugared_v.type do
            %AST.Hole{} ->
              Per.Typechecker.infer(acc.ctx, desugared_v.expr)

            _ ->
              Per.Typechecker.eval(desugared_v.type, acc.ctx)
          end

        eval_val = Per.Typechecker.eval(desugared_v.expr, acc.ctx)

        %{
          acc
          | defs: Map.put(acc.defs, desugared_v.name, eval_val),
            ctx: Map.put(acc.ctx, desugared_v.name, {:global, eval_ty, {:value, eval_val}})
        }

      _, acc ->
        acc
    end)
  end

  defp collect_local_names(%AST.Module{name: mod_name, declarations: decls}, env) do
    new_mapping =
      Enum.reduce(decls, env.name_to_mod, fn
        %AST.DeclValue{name: n}, acc ->
          Map.put(acc, n, mod_name)

        _, acc ->
          acc
      end)

    %{env | name_to_mod: new_mapping}
  end

  def resolve_imports(%AST.Module{name: mod_name, declarations: decls}, env, opts) do
    # Implicitly import Prelude if it exists and we are not in Prelude
    env =
      if mod_name != "Prelude" do
        case load_module_to_env("Prelude", env, opts) do
          {:ok, new_env} -> new_env
          _ -> env
        end
      else
        env
      end

    Enum.reduce(decls, env, fn
      {:import, name}, acc ->
        if MapSet.member?(acc.files, name) do
          acc
        else
          case load_module_to_env(name, acc, opts) do
            {:ok, new_env} -> new_env
            {:error, reason} -> raise "Failed to load module #{name}: #{inspect(reason)}"
          end
        end

      _, acc ->
        acc
    end)
  end

  def load_module_to_env(mod_name, env, opts \\ []) do
    if MapSet.member?(env.files, mod_name) do
      {:ok, env}
    else
      syntax = Keyword.get(opts, :syntax, :lean)
      lexer = case syntax do
        :agda -> Per.Lexer.Agda
        _ -> Per.Lexer
      end
      parser = case syntax do
        :agda -> Per.Parser.Agda
        _ -> Per.Parser
      end

      case find_module_path(mod_name, syntax) do
        {:ok, path} ->
          source = File.read!(path)

          with tokens <- lexer.lex(source),
               resolved <- Layout.resolve(tokens),
               {:ok, %AST.Module{} = mod, _} <- parser.parse(resolved) do
            # 1. Resolve imports of the sub-module first (recursive)
            env_with_imports = resolve_imports(mod, env, opts)

            # 2. Add declarations of the current module to env
            env_final = populate_local_env(mod, env_with_imports)
            env_with_names = collect_local_names(mod, env_final)
            {:ok, %{env_with_names | files: MapSet.put(env_with_names.files, mod_name)}}
          else
            err -> {:error, err}
          end

        nil ->
          {:error, :module_not_found}
      end
    end
  end

  def find_module_path(mod_name, syntax \\ :lean) do
    # Search in priv/per, test/per, and priv/foundations
    base_dir = if syntax == :agda, do: "priv/agda/", else: "priv/per/"
    test_dir = if syntax == :agda, do: "test/agda/", else: "test/per/"
    
    path1 = base_dir <> String.replace(mod_name, ".", "/") <> ".per"
    path2 = test_dir <> String.replace(mod_name, ".", "/") <> ".per"
    path3 = base_dir <> "foundations/" <> String.replace(mod_name, ".", "/") <> ".per"
    
    path4 = base_dir <> String.replace(mod_name, ".", "/") <> ".agda"
    path5 = base_dir <> "foundations/" <> String.replace(mod_name, ".", "/") <> ".agda"
    path6 = test_dir <> String.replace(mod_name, ".", "/") <> ".agda"

    cond do
      File.exists?(mod_name <> ".per") -> {:ok, mod_name <> ".per"}
      File.exists?(mod_name <> ".agda") -> {:ok, mod_name <> ".agda"}
      File.exists?(path1) -> {:ok, path1}
      File.exists?(path2) -> {:ok, path2}
      File.exists?(path3) -> {:ok, path3}
      File.exists?(path4) -> {:ok, path4}
      File.exists?(path5) -> {:ok, path5}
      File.exists?(path6) -> {:ok, path6}
      true -> nil
    end

  end

  def load_module(mod, bin) do
    :code.load_binary(mod, ~c"#{mod}.beam", bin)
  end

end
