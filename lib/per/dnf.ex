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

  def ext_and(v) do
    case v do
      %AST.And{left: x, right: y} -> Map.merge(ext_and(x), ext_and(y))
      %AST.Neg{expr: n} -> Map.new([{n, 0}])
      %AST.Dir{val: 1} -> %{}
      %AST.Dir{val: 0} -> raise "Zero in ext_and"
      atom -> Map.new([{atom, 1}])
    end
  end

  def ext_or(v) do
    case v do
      %AST.Or{left: x, right: y} -> MapSet.union(ext_or(x), ext_or(y))
      %AST.Dir{val: 0} -> MapSet.new()
      k -> MapSet.new([ext_and(k)])
    end
  end

  def uniq(t) do
    # Super x y = not (Conjunction.equal x y) && Conjunction.subset y x
    # subset y x means x contains all elements of y
    super_fn = fn x, y ->
      x != y and Enum.all?(y, fn {k, v} -> Map.get(x, k) == v end)
    end

    t
    |> Enum.filter(fn x ->
      not Enum.any?(t, fn other -> super_fn.(x, other) end)
    end)
    |> MapSet.new()
  end

  def unions(t1, t2) do
    res = for c1 <- t1, c2 <- t2, do: Map.merge(c1, c2)
    uniq(MapSet.new(res))
  end

  def neg_conjunction(c) do
    # Returns a disjunction
    c
    |> Enum.map(fn {x, d} -> %{x => 1 - d} end)
    |> MapSet.new()
  end

  def neg_disjunction(d) do
    Enum.reduce(d, MapSet.new([%{}]), fn c, res ->
      unions(res, neg_conjunction(c))
    end)
  end

  def contr_atom({atom, 0}), do: %AST.Neg{expr: atom}
  def contr_atom({atom, 1}), do: atom

  def contr_and(t) do
    Enum.reduce(t, %AST.Dir{val: 1}, fn e, acc ->
      and_formula(contr_atom(e), acc)
    end)
  end

  def contr_or(t) do
    Enum.reduce(t, %AST.Dir{val: 0}, fn e, acc ->
      or_formula(contr_and(e), acc)
    end)
  end

  def neg_formula(v) do
    case v do
      %AST.Dir{val: d} -> %AST.Dir{val: 1 - d}
      %AST.Neg{expr: n} -> n
      _ -> contr_or(neg_disjunction(ext_or(v)))
    end
  end

  def eval_and(a, b), do: contr_or(unions(ext_or(a), ext_or(b)))
  def eval_or(a, b), do: contr_or(uniq(MapSet.union(ext_or(a), ext_or(b))))

  def logic_eq(v1, v2) do
    ext_or(v1) == ext_or(v2)
  end
end
