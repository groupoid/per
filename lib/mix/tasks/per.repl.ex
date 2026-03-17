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
    foundations = ["mltt", "inductive", "univalent"]
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

    loop(env)
  end

  defp loop(env) do
    input = IO.gets("per> ")

    case input do
      nil ->
        :ok

      ":q\n" ->
        :ok

      "\n" ->
        loop(env)

      "import " <> rest ->
        mod_name = String.trim(rest)

        case Per.Compiler.load_module_to_env(mod_name, env) do
          {:ok, new_env} ->
            loop(new_env)

          {:error, err} ->
            IO.puts("Error: #{inspect(err)}")
            loop(env)
        end

      _ ->
        case eval(input, env) do
          {:ok, result} ->
            IO.puts("Result: #{AST.to_string(result)}")
            loop(env)

          {:error, err} ->
            IO.puts("Error: #{inspect(err)}")
            loop(env)
        end
    end
  end


  defp eval(input, env) do
    # Trim input
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
              desugared = Desugar.desugar_expression(expr, env)
              {:ok, Typechecker.normalize(env, desugared)}
            err -> {:error, err}
          end
      end
    end
  end
end
