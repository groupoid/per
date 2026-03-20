defmodule Per.DNF do
  alias Per.AST

  @doc """
  Disjunction of conjunctions.
  Conjunction is a map from variable name to direction (0 or 1).
  Disjunction is a MapSet of conjunction maps.
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

  def ext_or(v) do
    case v do
      %Per.AST.Dir{val: 0} -> MapSet.new()
      %Per.AST.Dir{val: 1} -> MapSet.new([%{}])
      %Per.AST.Or{left: x, right: y} -> MapSet.union(ext_or(x), ext_or(y))
      _ ->
        res = ext_and(v)
        MapSet.new([res])
    end
  end

  def ext_and(v) do
    case v do
      %Per.AST.And{left: x, right: y} ->
        c1 = ext_and(x)
        c2 = ext_and(y)
        Map.merge(c1, c2)
      %Per.AST.Neg{expr: %Per.AST.Var{name: name}} ->
        Map.new([{atom(name), 0}])
      %Per.AST.Var{name: name} ->
        Map.new([{atom(name), 1}])
      %Per.AST.Dir{val: 1} ->
        %{}
      %Per.AST.Neutral{term: t} ->
        ext_and(t)
      _ ->
        Map.new([{atom(v), 1}])
    end
  end

  def uniq(t) do
    # Optimization: A singleton set or empty set is already unique
    if MapSet.size(t) <= 1 do
      t
    else
      Prof.measure("uniq", fn ->
        # We want to remove any conjunction x that is "covered" by another more general conjunction y.
        # y covers x if y is a subset of x (less constraints).
        list = Enum.sort_by(t, &map_size/1)
        
        Enum.reduce(list, [], fn x, acc ->
          if Enum.any?(acc, fn y -> Map.merge(x, y) == x end) do
             acc
          else
             [x | acc]
          end
        end)
        |> MapSet.new()
      end)
    end
  end

  def unions(t1, t2) do
    # Optimization: If either is empty (False), return empty
    if MapSet.size(t1) == 0 or MapSet.size(t2) == 0 do
      MapSet.new()
    else
      Prof.measure("unions", fn ->
        res = for c1 <- t1, c2 <- t2,
                  {:ok, m} <- [meet(c1, c2)],
                  do: m
        uniq(MapSet.new(res))
      end)
    end
  end

  def neg_conjunction(c) do
    c
    |> Enum.map(fn {x, d} -> 
       %{atom(x) => 1 - d}
    end)
    |> MapSet.new()
  end

  def neg_disjunction(d) do
    Enum.reduce(d, MapSet.new([%{}]), fn c, res ->
      unions(res, neg_conjunction(c))
    end)
  end

  def contr_atom({atom, 0}), do: %Per.AST.Neg{expr: %Per.AST.Var{name: atom(atom)}}
  def contr_atom({atom, 1}), do: %Per.AST.Var{name: atom(atom)}

  def contr_and(t) do
    Enum.reduce(t, %Per.AST.Dir{val: 1}, fn e, acc ->
      and_formula(contr_atom(e), acc)
    end)
  end

  def contr_or(t) do
    Enum.reduce(t, %Per.AST.Dir{val: 0}, fn e, acc ->
      or_formula(contr_and(e), acc)
    end)
  end

  def neg_formula(v) do
    case v do
      %Per.AST.Dir{val: d} -> %Per.AST.Dir{val: 1 - d}
      %Per.AST.Neg{expr: n} -> n
      _ -> contr_or(neg_disjunction(ext_or(v)))
    end
  end

  def eval_and(a, b) do
    contr_or(unions(ext_or(a), ext_or(b)))
  end

  def eval_or(a, b) do
    contr_or(uniq(MapSet.union(ext_or(a), ext_or(b))))
  end


  def solve(v, val) do
    Prof.measure("solve", fn ->
      if val == 1 do
         ext_or(v)
      else
         ext_or(neg_formula(v))
      end
    end)
  end

  def getFaceV(face) do
    Enum.reduce(face, %Per.AST.Dir{val: 1}, fn {name, val}, acc ->
      atom = %Per.AST.Var{name: atom(name)}
      term = if val == 1, do: atom, else: %Per.AST.Neg{expr: atom}
      eval_and(acc, term)
    end)
  end

  def getFormulaV(map) do
    Enum.reduce(map, %Per.AST.Dir{val: 0}, fn {face, _val}, acc ->
      fv = getFaceV(face)
      eval_or(fv, acc)
    end)
  end

  def meet(f1, f2) do
    f1 = if is_map(f1), do: f1, else: Map.new(f1)
    f2 = if is_map(f2), do: f2, else: Map.new(f2)
    try do
      res = Map.merge(f1, f2, fn _k, v1, v2 ->
        if v1 == v2, do: v1, else: throw(:incompatible)
      end)
      {:ok, res}
    catch
      :incompatible -> :error
    end
  end

  def meets(xs, ys) do
    (for x <- xs, y <- ys, match?({:ok, _}, meet(x, y)), do: elem(meet(x, y), 1))
    |> Enum.uniq()
  end

  def logic_eq(v1, v2) do
    Prof.measure("logic_eq", fn ->
      ext_or(v1) == ext_or(v2)
    end)
  end
end
