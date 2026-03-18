defmodule Mix.Tasks.Per.Test do
  use Mix.Task

  @shortdoc "Run Per tests"
  def run(args) do
    {opts, _, _} = OptionParser.parse(args, switches: [syntax: :string])
    syntax_str = Keyword.get(opts, :syntax, "lean")
    syntax = String.to_atom(syntax_str)

    IO.puts("Running Per tests [#{syntax_str}]...")

    test_dir = if syntax == :agda, do: "test/agda", else: "test/per"
    test_files = Path.wildcard("#{test_dir}/**/*.per") ++ Path.wildcard("#{test_dir}/**/*.agda")

    # Preload foundational modules
    base_env = %Per.Typechecker.Env{}
    {:ok, base_env} = Per.Compiler.load_module_to_env("mltt", base_env, [syntax: syntax])
    {:ok, base_env} = Per.Compiler.load_module_to_env("inductive", base_env, [syntax: syntax])

    results =
      Enum.map(test_files, fn file ->
        IO.write("  Testing #{file}... ")
        source = File.read!(file)

        case Per.Compiler.compile_module(source, [source_path: file, env: base_env, syntax: syntax] ++ opts) do
          {:ok, mod, _bin} ->
            IO.puts("OK (#{mod})")
            :ok

          err ->
            IO.puts("FAILED: #{inspect(err)}")
            :error
        end
      end)


    failures = Enum.count(results, &(&1 == :error))

    if failures > 0 do
      IO.puts("\n#{failures} tests failed.")
      System.halt(1)
    else
      IO.puts("\nAll Per tests passed.")
    end
  end
end
