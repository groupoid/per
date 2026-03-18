defmodule Mix.Tasks.Per.Repl do
  use Mix.Task

  alias Per.{Layout, Desugar, Typechecker, AST}

  @shortdoc "Per interactive REPL"
  def run(_) do
    IO.puts("🧊 Per Programming Language version 0.4.0\n" <>
            "Copyright (c) 2016-2026 Groupoid Infinity\n" <>
            "https://groupoid.github.io/per/\n"
            )
    env = %Typechecker.Env{}
    syntax = :lean

    # Auto-load foundations
    foundations = ["mltt", "inductive", "univalent", "homotopical"]
    env =
      Enum.reduce(foundations, env, fn mod_name, acc_env ->
        case Per.Compiler.load_module_to_env(mod_name, acc_env, [syntax: syntax]) do
          {:ok, new_env} ->
            IO.puts("Loaded: #{mod_name}")
            new_env

          {:error, _err} ->
             acc_env
        end
      end)

    loop(env, syntax)
  end

  defp loop(env, syntax) do
    syntax_name = if syntax == :agda, do: "Agda", else: "Lean"
    input = IO.gets("per [#{syntax_name}]> ")

    case input do
      nil -> :ok
      ":q\n" -> :ok
      "\n" -> loop(env, syntax)

      ":syntax agda\n" ->
        IO.puts("Switched to Agda syntax")
        loop(env, :agda)

      ":syntax lean\n" ->
        IO.puts("Switched to Lean syntax")
        loop(env, :lean)

      ":check " <> rest ->
        handle_introspection(String.trim(rest), :check, env, syntax)
        loop(env, syntax)

      ":eval " <> rest ->
        handle_introspection(String.trim(rest), :eval, env, syntax)
        loop(env, syntax)

      ":print " <> rest ->
        handle_introspection(String.trim(rest), :print, env, syntax)
        loop(env, syntax)

      "import " <> rest ->
        mod_name = String.trim(rest)
        case Per.Compiler.load_module_to_env(mod_name, env, [syntax: syntax]) do
          {:ok, new_env} ->
            IO.puts("Loaded: #{mod_name}")
            loop(new_env, syntax)

          {:error, err} ->
            IO.puts("Error: #{inspect(err)}")
            loop(env, syntax)
        end

      _ ->
        case eval(input, env, syntax) do
          {:ok, result} ->
            IO.puts("Result: #{AST.to_string(result)}")
            loop(env, syntax)

          {:error, err} ->
            IO.puts("Error: #{inspect(err)}")
            loop(env, syntax)
        end
    end
  end

  defp handle_introspection(input, mode, env, syntax) do
    case parse_and_desugar(input, env, syntax) do
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

  defp parse_and_desugar(input, env, syntax) do
    input = String.trim(input)
    if input == "" do
      {:error, :empty_input}
    else
      lexer = if syntax == :agda, do: Per.Lexer.Agda, else: Per.Lexer
      parser = if syntax == :agda, do: Per.Parser.Agda, else: Per.Parser

      case lexer.lex(input) do
        {:error, _} = err -> err
        tokens ->
          resolved = Layout.resolve(tokens)
          case parser.parse_expression(resolved) do
            {:ok, expr, _} ->
              {:ok, Desugar.desugar_expression(expr, env)}
            err -> {:error, err}
          end
      end
    end
  end

  defp eval(input, env, syntax) do
    case parse_and_desugar(input, env, syntax) do
      {:ok, term} -> {:ok, Typechecker.normalize(env, term)}
      err -> err
    end
  end

end
