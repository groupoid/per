defmodule Mix.Tasks.Per.Base do
  use Mix.Task

  @shortdoc "Compile Per standard library"
  def run(args) do
    {opts, _, _} = OptionParser.parse(args, switches: [check_only: :boolean])
    check_only = Keyword.get(opts, :check_only, false)

    if check_only do
      IO.puts("Typechecking Per base library...")
    else
      IO.puts("Compiling Per base library...")
    end

    # Order matters for the base library
    base_files = [
      "priv/per/foundations/mltt.per",
      "priv/per/foundations/inductive.per",
      "priv/per/foundations/univalent.per"
    ]

    out_dir = "ebin"
    File.mkdir_p!(out_dir)

    results = Enum.map(base_files, fn file ->
      if File.exists?(file) do
        action_str = if check_only, do: "Checking", else: "Compiling"
        IO.write("  #{action_str} #{file}... ")
        source = File.read!(file)

        case Per.Compiler.compile_module(source, [source_path: file] ++ opts) do
          {:ok, _mod, :check_only} ->
            IO.puts("OK (Checked)")
            :ok

          {:ok, mod, bin} ->
            beam_path = Path.join(out_dir, "#{mod}.beam")
            File.write!(beam_path, bin)
            IO.puts("OK")
            :ok

          {:error, reason} ->
            IO.puts("FAILED: #{inspect(reason, pretty: true)}")
            :error
        end
      else
        :ok
      end
    end)

    failures = Enum.count(results, &(&1 == :error))

    finished_str = if check_only, do: "verification", else: "compilation"
    if failures > 0 do
      IO.puts("\nPer base library #{finished_str} FAILED with #{failures} errors.")
      System.halt(1)
    else
      IO.puts("\nPer base library #{finished_str} finished successfully.")
    end
  end
end
