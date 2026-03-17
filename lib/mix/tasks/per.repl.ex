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

    # Auto-load all modules from priv/per and test/per
    # and also Prelude if possible
    env =
      case Per.Compiler.load_module_to_env("Prelude", env) do
        {:ok, new_env} -> new_env
        _ -> env
      end

    paths = Path.wildcard("{priv,test}/per/**/*.per")

    env =
      Enum.reduce(paths, env, fn path, acc_env ->
        parts = Path.split(path)
        mod_parts =
          parts
          |> Enum.drop_while(&(&1 != "per"))
          |> Enum.drop(1)
          |> List.update_at(-1, &Path.rootname/1)

        mod_name = Enum.join(mod_parts, ".")

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
      with {:ok, tokens} <- Lexer.lex(input),
           resolved <- Layout.resolve(tokens),
           {:ok, expr, _} <- Parser.parse_expression(resolved) do
        desugared = Desugar.desugar_expression(expr, env)
        # Normalize
        {:ok, Typechecker.normalize(env, desugared)}
      else
        err -> {:error, err}
      end
    end
  end
end
