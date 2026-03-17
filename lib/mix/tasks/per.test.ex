defmodule Mix.Tasks.Per.Test do
  use Mix.Task

  @shortdoc "Run Per tests"
  def run(_) do
    IO.puts("Running Per tests...")

    test_files = Path.wildcard("test/per/**/*.per")

    results =
      Enum.map(test_files, fn file ->
        IO.write("  Testing #{file}... ")
        source = File.read!(file)

        case Per.Compiler.compile_module(source, source_path: file) do
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
