defmodule Prof do
  @moduledoc """
  Profiling utility for the Per compiler.
  Used to measure execution time of different compilation phases.
  """

  @doc "Starts the profiler."
  def start() do
    Process.put(:prof_data, %{})
    Process.put(:prof_depth, 0)
    Process.put(:prof_active, true)
  end

  @doc "Stops the profiler."
  def stop() do
    Process.put(:prof_active, false)
  end

  @doc "Measures the execution time of a function."
  def measure(name, func) do
    if Process.get(:prof_active) do
      depth = Process.get(:prof_depth, 0)
      Process.put(:prof_depth, depth + 1)
      start_time = :os.timestamp()
      res = func.()
      end_time = :os.timestamp()
      time = :timer.now_diff(end_time, start_time)
      Process.put(:prof_depth, depth)

      data = Process.get(:prof_data, %{})
      key = {name, depth}
      {count, total_time} = Map.get(data, key, {0, 0})
      Process.put(:prof_data, Map.put(data, key, {count + 1, total_time + time}))
      res
    else
      func.()
    end
  end

  @doc "Prints the collected profiling data."
  def print() do
    data = Process.get(:prof_data, %{})

    if data == %{} do
      IO.puts("No profiling data collected.")
    else
      # Sort by depth then name
      sorted =
        Enum.sort(data, fn {{n1, d1}, _}, {{n2, d2}, _} ->
          if d1 == d2, do: n1 < n2, else: d1 < d2
        end)

      total_time =
        case Map.get(data, {"Total", 0}) do
          {_, t} -> t
          nil -> Enum.map(data, fn {_, {_, t}} -> t end) |> Enum.max()
        end

      max_width = 40
      IO.puts("")
      Enum.each(sorted, fn {{name, depth}, {count, time}} ->
        indent = String.duplicate("  ", depth)
        per = time / total_time
        bar_len = round(per * max_width)
        bar = String.duplicate("=", bar_len) <> String.duplicate(" ", max_width - bar_len)
        ts = :erlang.float_to_binary(time / 1_000_000, decimals: 6)
        name_width = max(0, 50 - depth * 2)
        IO.puts("#{indent}#{String.pad_trailing(name, name_width)} [#{bar}] #{ts}s (x#{count})")
      end)
    end
  end
end
