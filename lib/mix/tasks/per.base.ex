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
      "priv/foundations/mltt.per",
      "priv/foundations/inductive.per",
      "priv/foundations/either.per"
    ]

    out_dir = "ebin"
    File.mkdir_p!(out_dir)

    Enum.each(base_files, fn file ->
      if File.exists?(file) do
        action_str = if check_only, do: "Checking", else: "Compiling"
        IO.write("  #{action_str} #{file}... ")
        source = File.read!(file)

        case Per.Compiler.compile_module(source, [source_path: file] ++ opts) do
          {:ok, _mod, :check_only} ->
            IO.puts("OK (Checked)")

          {:ok, mod, bin} ->
            beam_path = Path.join(out_dir, "#{mod}.beam")
            File.write!(beam_path, bin)
            IO.puts("OK")

          {:error, reason} ->
            IO.puts("FAILED: #{inspect(reason, pretty: true)}")
        end
      end
    end)

    finished_str = if check_only, do: "verification", else: "compilation"
    IO.puts("\nPer base library #{finished_str} finished.")
  end
end
