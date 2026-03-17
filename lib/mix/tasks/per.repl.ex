defmodule Mix.Tasks.Per.Repl do
  use Mix.Task

  alias Per.{Lexer, Layout, Parser, Desugar, Typechecker, AST}

  @shortdoc "Per interactive REPL"
  def run(_) do
    IO.puts("🧊 Per Programming Language version 0.4.0 [Lean Syntax]\n" <>
            "Copyright (c) 2016-2026 Groupoid Infinity\n" <>
            "https://groupoid.github.io/per/\n"
            )
    env = %Typechecker.Env{}

    # Auto-load foundations
    foundations = ["mltt", "inductive", "univalent", "homotopical"]
    env =
      Enum.reduce(foundations, env, fn mod_name, acc_env ->
        case Per.Compiler.load_module_to_env(mod_name, acc_env) do
          {:ok, new_env} ->
            IO.puts("Loaded: #{mod_name}")
            new_env

          {:error, _err} ->
             acc_env
        end
      end)

    loop(env, "Lean")
  end

  defp loop(env, syntax_name) do
    input = IO.gets("per> ")

    case input do
      nil -> :ok
      ":q\n" -> :ok
      "\n" -> loop(env, syntax_name)

      ":check " <> rest ->
        handle_introspection(String.trim(rest), :check, env)
        loop(env, syntax_name)

      ":eval " <> rest ->
        handle_introspection(String.trim(rest), :eval, env)
        loop(env, syntax_name)

      ":print " <> rest ->
        handle_introspection(String.trim(rest), :print, env)
        loop(env, syntax_name)

      "import " <> rest ->
        mod_name = String.trim(rest)
        case Per.Compiler.load_module_to_env(mod_name, env) do
          {:ok, new_env} ->
            IO.puts("Loaded: #{mod_name}")
            loop(new_env, syntax_name)

          {:error, err} ->
            IO.puts("Error: #{inspect(err)}")
            loop(env, syntax_name)
        end

      _ ->
        case eval(input, env) do
          {:ok, result} ->
            IO.puts("Result: #{AST.to_string(result)}")
            loop(env, syntax_name)

          {:error, err} ->
            IO.puts("Error: #{inspect(err)}")
            loop(env, syntax_name)
        end
    end
  end

  defp handle_introspection(input, mode, env) do
    case parse_and_desugar(input, env) do
      {:ok, term} ->
        # For :check and :eval, we need the type
        case mode do
          :check ->
            try do
              ty = Typechecker.infer(env.ctx, term)
              IO.puts("TYPE: #{AST.to_string(Typechecker.readback(ty))}")
            rescue
              e -> IO.puts("Type Error: #{inspect(e)}")
            end

          :eval ->
            try do
              ty = Typechecker.infer(env.ctx, term)
              norm = Typechecker.normalize(env, term)
              IO.puts("TYPE: #{AST.to_string(Typechecker.readback(ty))}")
              IO.puts("TERM: #{AST.to_string(norm)}")
            rescue
              e -> IO.puts("Error: #{inspect(e)}")
            end

          :print ->
            try do
              ty = Typechecker.infer(env.ctx, term)
              IO.puts("TYPE: #{AST.to_string(Typechecker.readback(ty))}")
              IO.puts("TERM: #{AST.to_string(term)}")
            rescue
              e -> IO.puts("Error: #{inspect(e)}")
            end
        end

      {:error, err} ->
        IO.puts("Error: #{inspect(err)}")
    end
  end

  defp parse_and_desugar(input, env) do
    input = String.trim(input)
    if input == "" do
      {:error, :empty_input}
    else
      case Lexer.lex(input) do
        {:error, _} = err -> err
        tokens ->
          resolved = Layout.resolve(tokens)
          case Parser.parse_expression(resolved) do
            {:ok, expr, _} ->
              {:ok, Desugar.desugar_expression(expr, env)}
            err -> {:error, err}
          end
      end
    end
  end

  defp eval(input, env) do
    case parse_and_desugar(input, env) do
      {:ok, term} -> {:ok, Typechecker.normalize(env, term)}
      err -> err
    end
  end
end
