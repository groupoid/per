defmodule Mix.Tasks.Per.Base do
  use Mix.Task

  @shortdoc "Compile Per standard library"
  def run(args) do
    {opts, _, _} = OptionParser.parse(args, switches: [check_only: :boolean, syntax: :string])
    check_only = Keyword.get(opts, :check_only, false)
    syntax_str = Keyword.get(opts, :syntax, "lean")
    syntax = String.to_atom(syntax_str)

    if check_only do
      IO.puts("Typechecking Per base library [#{syntax_str}]...")
    else
      IO.puts("Compiling Per base library [#{syntax_str}]...")
    end

    # Order matters for the base library
    base_dir = if syntax == :agda, do: "priv/agda/", else: "priv/per/"
    
    base_files = [
      Path.join(base_dir, "foundations/mltt.per"),
      Path.join(base_dir, "foundations/inductive.per"),
      Path.join(base_dir, "foundations/univalent.per")
    ]

    # Also check for .agda extension
    base_files = Enum.flat_map(base_files, fn f ->
      if File.exists?(f) do
        [f]
      else
        agda_f = String.replace(f, ".per", ".agda")
        if File.exists?(agda_f), do: [agda_f], else: [f]
      end
    end)

    out_dir = "ebin"
    File.mkdir_p!(out_dir)

    results = Enum.map(base_files, fn file ->
      if File.exists?(file) do
        action_str = if check_only, do: "Checking", else: "Compiling"
        IO.write("  #{action_str} #{file}... ")
        source = File.read!(file)

        case Per.Compiler.compile_module(source, [source_path: file, syntax: syntax] ++ opts) do
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

          {:error, reason, details} ->
            IO.puts("FAILED: #{inspect(reason, pretty: true)} -> #{inspect(details, pretty: true)}")
            :error
        end
      else
        IO.puts("SKIPPED: #{file} not found")
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
