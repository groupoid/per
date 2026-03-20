defmodule Per.DNF do
  @moduledoc """
  DNF (Disjunctive Normal Form) solver for cubical formulas.
  Used for solving face constraints and checking equivalence of formulas.
  """
  alias Per.AST
  import Bitwise

  # --- Bitset Face Representation ---

  @doc "Converts a face map to a bitset representation."
  def to_bits(map, index) do
    Enum.reduce(map, {0, 0}, fn {name, val}, {mask, values} ->
      pos = Map.get(index, name)
      bit = 1 <<< pos
      mask = mask ||| bit
      values = if val == 1, do: values ||| bit, else: values
      {mask, values}
    end)
  end

  @doc "Converts a bitset representation back to a face map."
  def from_bits({mask, values}, inv_index) do
    for i <- 0..63, ((mask >>> i) &&& 1) == 1, into: %{} do
      name = Map.get(inv_index, i)
      val = if ((values >>> i) &&& 1) == 1, do: 1, else: 0
      {name, val}
    end
  end

  # --- Bitwise DNF Operations ---

  @doc """
  Surface-level OR formula constructor with basic simplifications.
  Disjunction of conjunctions.
  Conjunction is a pair of integers {mask, values}.
  Disjunction is a MapSet of conjunction pairs.
  """
  def or_formula(a, b) do
    case {a, b} do
      {%AST.Dir{val: 1}, _} -> %AST.Dir{val: 1}
      {_, %AST.Dir{val: 1}} -> %AST.Dir{val: 1}
      {%AST.Dir{val: 0}, f} -> f
      {f, %AST.Dir{val: 0}} -> f
      {f, g} -> if f == g, do: f, else: %AST.Or{left: f, right: g}
    end
  end

  @doc "Surface-level AND formula constructor with basic simplifications."
  def and_formula(a, b) do
    case {a, b} do
      {%AST.Dir{val: 0}, _} -> %AST.Dir{val: 0}
      {_, %AST.Dir{val: 0}} -> %AST.Dir{val: 0}
      {%AST.Dir{val: 1}, f} -> f
      {f, %AST.Dir{val: 1}} -> f
      {f, g} -> if f == g, do: f, else: %AST.And{left: f, right: g}
    end
  end

  defp atom(v) do
    case v do
      %Per.AST.Var{name: n} -> atom(n)
      %Per.AST.Neutral{term: t} -> atom(t)
      n when is_binary(n) -> n
      _ -> v
    end
  end

  defp memo(key, func) do
    memo_key = {:dnf_memo, key}
    case Process.get(memo_key) do
      nil ->
        res = func.()
        Process.put(memo_key, res)
        res
      res -> res
    end
  end

  @doc "Extracts disjunction (Set of conjunctions) from a formula."
  def ext_or(v, index \\ nil) do
    memo({:ext_or, v, index}, fn ->
      case v do
        %AST.Dir{val: 0} -> MapSet.new()
        %AST.Dir{val: 1} -> MapSet.new([if(index, do: {0, 0}, else: %{})])
        %AST.Or{left: x, right: y} -> MapSet.union(ext_or(x, index), ext_or(y, index))
        _ ->
          if index do
            MapSet.new([ext_and_bits(v, index)])
          else
            MapSet.new([ext_and(v)])
          end
      end
    end)
  end

  @doc "Extracts conjunction (map) from an AND-formula."
  def ext_and(v) do
    case v do
      %AST.And{left: x, right: y} -> Map.merge(ext_and(x), ext_and(y))
      %AST.Neg{expr: %AST.Var{name: name}} -> %{atom(name) => 0}
      %AST.Var{name: name} -> %{atom(name) => 1}
      %AST.Dir{val: 1} -> %{}
      %AST.Neutral{term: t} -> ext_and(t)
      _ -> %{atom(v) => 1}
    end
  end

  @doc "Extracts conjunction (bitset) from an AND-formula."
  def ext_and_bits(v, index) do
    case v do
      %AST.And{left: x, right: y} ->
        {m1, v1} = ext_and_bits(x, index)
        {m2, v2} = ext_and_bits(y, index)
        {m1 ||| m2, v1 ||| v2}
      %AST.Neg{expr: %AST.Var{name: name}} ->
        pos = Map.get(index, atom(name))
        {1 <<< pos, 0}
      %AST.Var{name: name} ->
        pos = Map.get(index, atom(name))
        {1 <<< pos, 1 <<< pos}
      %AST.Dir{val: 1} -> {0, 0}
      %AST.Neutral{term: t} -> ext_and_bits(t, index)
      _ ->
        pos = Map.get(index, atom(v))
        {1 <<< pos, 1 <<< pos}
    end
  end

  @doc "Removes redundant conjunctions from a disjunction."
  def uniq(t) do
    size = MapSet.size(t)
    if size <= 1 do
      t
    else
      memo({:uniq, t}, fn ->
        list = MapSet.to_list(t)
        res = case list do
          [x, y] -> 
            if covers?(x, y), do: [x], else: (if covers?(y, x), do: [y], else: [x, y])
          _ ->
            sorted = Enum.sort_by(list, fn 
              {m, _} -> bit_count(m) 
              m when is_map(m) -> map_size(m)
            end)
            Enum.reduce(sorted, [], fn x, acc ->
              if Enum.any?(acc, fn y -> covers?(y, x) end), do: acc, else: [x | acc]
            end)
        end
        MapSet.new(res)
      end)
    end
  end

  defp bit_count(n), do: do_bit_count(n, 0)
  defp do_bit_count(0, acc), do: acc
  defp do_bit_count(n, acc), do: do_bit_count(n &&& (n - 1), acc + 1)

  defp covers?({m1, v1}, {m2, v2}) do
    (m2 &&& m1) == m1 and (v2 &&& m1) == v1
  end
  defp covers?(y, x) when is_map(x) and is_map(y) do
    Map.merge(x, y) == x
  end

  @doc "Computes intersection of two disjunctions (distributes AND over OR)."
  def unions(t1, t2) do
    if MapSet.size(t1) == 0 or MapSet.size(t2) == 0 do
      MapSet.new()
    else
      memo({:unions, t1, t2}, fn ->
        res = for c1 <- t1, c2 <- t2,
                  {:ok, m} <- [meet(c1, c2)],
                  do: m
        uniq(MapSet.new(res))
      end)
    end
  end

  @doc "Computes intersection of two conjunctions."
  def meet({m1, v1}, {m2, v2}) do
    if (bxor(v1, v2) &&& m1 &&& m2) == 0 do
      {:ok, {m1 ||| m2, v1 ||| v2}}
    else
      :error
    end
  end
  def meet(f1, f2) when is_map(f1) and is_map(f2) do
    try do
      res = Map.merge(f1, f2, fn _k, v1, v2 ->
        if v1 == v2, do: v1, else: throw(:incompatible)
      end)
      {:ok, res}
    catch
      :incompatible -> :error
    end
  end

  @doc "Computes the negation of a conjunction."
  def neg_conjunction({mask, values}, _index) do
    # Negation of (a1 & a2 & ...) is (~a1 | ~a2 | ...)
    for i <- 0..63, ((mask >>> i) &&& 1) == 1, into: MapSet.new() do
      bit = 1 <<< i
      val = if (values &&& bit) == 0, do: bit, else: 0
      {bit, val}
    end
  end
  def neg_conjunction(c, _index) when is_map(c) do
    for {x, d} <- c, into: MapSet.new() do
      %{atom(x) => 1 - d}
    end
  end

  @doc "Computes the negation of a disjunction."
  def neg_disjunction(d, index \\ nil) do
    init = MapSet.new([if(index, do: {0, 0}, else: %{})])
    Enum.reduce(d, init, fn c, res ->
      unions(res, neg_conjunction(c, index))
    end)
  end

  @doc "Computes the negation of a formula."
  def neg_formula(v, index \\ nil) do
    case v do
      %AST.Dir{val: d} -> %AST.Dir{val: 1 - d}
      %AST.Neg{expr: n} -> n
      _ -> contr_or(neg_disjunction(ext_or(v, index), index), index)
    end
  end

  @doc "Converts a conjunction element back to an AST formula."
  def contr_atom({mask, values}, inv_index) do
    # For bitsets, conjunctions in disjunction are singletons
    i = find_bit(mask)
    name = Map.get(inv_index, i)
    val = if ((values >>> i) &&& 1) == 1, do: 1, else: 0
    if val == 0, do: %AST.Neg{expr: %AST.Var{name: name}}, else: %AST.Var{name: name}
  end
  def contr_atom({atom, 0}), do: %AST.Neg{expr: %AST.Var{name: atom(atom)}}
  def contr_atom({atom, 1}), do: %AST.Var{name: atom(atom)}

  defp find_bit(n, i \\ 0) do
    if ((n >>> i) &&& 1) == 1, do: i, else: find_bit(n, i + 1)
  end

  @doc "Converts a conjunction back to an AST formula."
  def contr_and({m, v}, inv_index) do
    # Bitset conjunction to formula
    for i <- 0..63, ((m >>> i) &&& 1) == 1 do
       {1 <<< i, v &&& (1 <<< i)}
    end
    |> Enum.reduce(%AST.Dir{val: 1}, fn e, acc ->
      and_formula(contr_atom(e, inv_index), acc)
    end)
  end
  def contr_and(t) when is_map(t) do
    Enum.reduce(t, %AST.Dir{val: 1}, fn e, acc ->
      and_formula(contr_atom(e), acc)
    end)
  end

  @doc "Converts a disjunction back to an AST formula."
  def contr_or(t, index \\ nil) do
    inv_index = if index, do: Map.new(Enum.map(index, fn {k, v} -> {v, k} end))
    Enum.reduce(t, %AST.Dir{val: 0}, fn e, acc ->
      f = if index, do: contr_and(e, inv_index), else: contr_and(e)
      or_formula(f, acc)
    end)
  end

  @doc "Evaluates AND of two formulas via DNF."
  def eval_and(a, b), do: contr_or(unions(ext_or(a), ext_or(b)))
  @doc "Evaluates OR of two formulas via DNF."
  def eval_or(a, b), do: contr_or(uniq(MapSet.union(ext_or(a), ext_or(b))))

  @doc "Solves a formula for a given value (1 or 0), returning a disjunction."
  def solve(v, val, index \\ nil) do
    if val == 1 do
      ext_or(v, index)
    else
      ext_or(neg_formula(v, index), index)
    end
  end

  @doc "Checks if two formulas are logically equivalent."
  def logic_eq(v1, v2) do
    if v1 === v2 do
      true
    else
      memo({:logic_eq, v1, v2}, fn ->
        case {v1, v2} do
          {%AST.Dir{val: d1}, %AST.Dir{val: d2}} -> d1 == d2
          _ ->
            # For cubes, we can collect atoms and use bitsets
            atoms = AST.collect_atoms(%AST.And{left: v1, right: v2})
            index = Map.new(Enum.with_index(atoms))
            ext_or(v1, index) == ext_or(v2, index)
        end
      end)
    end
  end

  @doc "Converts a face map to an AST formula value."
  def getFaceV(face) do
    Enum.reduce(face, %Per.AST.Dir{val: 1}, fn {name, val}, acc ->
      atom = %Per.AST.Var{name: atom(name)}
      term = if val == 1, do: atom, else: %Per.AST.Neg{expr: atom}
      eval_and(acc, term)
    end)
  end

  @doc "Converts a system map to an AST formula value."
  def getFormulaV(map) do
    Enum.reduce(map, %Per.AST.Dir{val: 0}, fn {face, _val}, acc ->
      fv = getFaceV(face)
      eval_or(fv, acc)
    end)
  end

  @doc "Intersection of two lists of faces."
  def meets(xs, ys) do
    (for x <- xs, y <- ys, match?({:ok, _}, meet(x, y)), do: elem(meet(x, y), 1))
    |> Enum.uniq()
  end
end
