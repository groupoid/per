defmodule Per.AST do
  import Kernel, except: [to_string: 1]

  @moduledoc """
  Abstract Syntax Tree structures for the Per compiler.
  """

  # --- Surface Language Declarations ---

  defmodule Neutral do
    @moduledoc "Neutral term with its type."
    defstruct [:term, :type]
  end

  defmodule Module do
    @moduledoc "A module containing a name and declarations."
    defstruct [:name, :declarations]
  end

  defmodule DeclValue do
    @moduledoc "A value declaration with name, type, expression, and optional guards/WHERE clauses."
    defstruct [:name, :type, :expr, :guards, :where_decls]
  end

  defmodule DeclTypeSignature do
    @moduledoc "A type signature declaration (axiom)."
    defstruct [:name, :type]
  end

  defmodule DeclForeign do
    @moduledoc "A foreign function declaration."
    defstruct [:name, :type, :erl_mod, :erl_func]
  end

  defmodule Let do
    @moduledoc "A let-expression."
    defstruct [:name, :type, :val, :body]
  end

  # --- Core Language Terms ---

  defmodule Var do
    @moduledoc "A variable."
    defstruct [:name]
  end

  defmodule Universe do
    @moduledoc "A universe type at a given level."
    defstruct [:level]
  end

  defmodule Type do
    @moduledoc "A type at a given cosmos and level."
    defstruct [:cosmos, :level]
  end

  defmodule Pi do
    @moduledoc "A dependent function type."
    defstruct [:name, :domain, :codomain]
  end

  defmodule Lam do
    @moduledoc "A lambda abstraction."
    defstruct [:name, :domain, :body]
  end

  defmodule App do
    @moduledoc "Function application."
    defstruct [:func, :arg]
  end

  defmodule Hole do
    @moduledoc "A placeholder hole."
    defstruct []
  end

  defmodule Sigma do
    @moduledoc "A dependent pair type."
    defstruct [:name, :domain, :codomain]
  end

  defmodule Pair do
    @moduledoc "A pair of terms."
    defstruct [:first, :second, tag: nil]
  end

  defmodule Fst do
    @moduledoc "First projection of a pair."
    defstruct [:expr]
  end

  defmodule Snd do
    @moduledoc "Second projection of a pair."
    defstruct [:expr]
  end

  defmodule Field do
    @moduledoc "Field projection of a record."
    defstruct [:expr, :name]
  end

  defmodule Id do
    @moduledoc "Identity type."
    defstruct [:type]
  end

  defmodule Refl do
    @moduledoc "Reflexivity term."
    defstruct [:expr]
  end

  defmodule IdJ do
    @moduledoc "Identity J-eliminator."
    defstruct [:expr]
  end

  defmodule PathP do
    @moduledoc "Path type."
    defstruct [:path, :u0, :u1]
  end

  defmodule PLam do
    @moduledoc "Path lambda abstraction."
    defstruct [:name, :body]
  end

  defmodule AppFormula do
    @moduledoc "Formula application (at-sign)."
    defstruct [:left, :right]
  end

  defmodule Interval do
    @moduledoc "Interval type I."
    defstruct []
  end

  defmodule Dir do
    @moduledoc "Direction (0 or 1)."
    defstruct [:val] # 0 or 1
  end

  defmodule And do
    @moduledoc "Logical AND formula."
    defstruct [:left, :right]
  end

  defmodule Or do
    @moduledoc "Logical OR formula."
    defstruct [:left, :right]
  end

  defmodule Neg do
    @moduledoc "Logical NEG formula."
    defstruct [:expr]
  end

  defmodule Transp do
    @moduledoc "Transport operation."
    defstruct [:path, :phi]
  end

  defmodule HComp do
    @moduledoc "Homogeneous composition operation."
    defstruct [:type, :phi, :u, :u0]
  end

  defmodule Partial do
    @moduledoc "Partial type."
    defstruct [:expr]
  end

  defmodule PartialP do
    @moduledoc "PartialP type."
    defstruct [:type, :phi]
  end

  defmodule System do
    @moduledoc "System term (map of face -> expr)."
    defstruct [:map] # map of face -> expr
  end

  defmodule Sub do
    @moduledoc "Sub type."
    defstruct [:type, :phi, :u]
  end

  defmodule Inc do
    @moduledoc "inc operation."
    defstruct [:type, :phi]
  end

  defmodule Ouc do
    @moduledoc "ouc operation."
    defstruct [:expr]
  end

  defmodule Glue do
    @moduledoc "Glue type."
    defstruct [:type]
  end

  defmodule GlueElem do
    @moduledoc "GlueElem term."
    defstruct [:phi, :u, :a]
  end

  defmodule Unglue do
    @moduledoc "Unglue term."
    defstruct [:phi, :u, :e]
  end

  defmodule Empty do
    @moduledoc "Empty type."
    defstruct []
  end

  defmodule IndEmpty do
    @moduledoc "IndEmpty eliminator."
    defstruct [:type]
  end

  defmodule Unit do
    @moduledoc "Unit type."
    defstruct []
  end

  defmodule Star do
    @moduledoc "Star term (unit constant)."
    defstruct []
  end

  defmodule IndUnit do
    @moduledoc "IndUnit eliminator."
    defstruct [:type]
  end

  defmodule Bool do
    @moduledoc "Boolean type."
    defstruct []
  end

  defmodule FalseConstant do
    @moduledoc "False constant (0₂)."
    defstruct []
  end

  defmodule TrueConstant do
    @moduledoc "True constant (1₂)."
    defstruct []
  end

  defmodule IndBool do
    @moduledoc "IndBool eliminator."
    defstruct [:type]
  end

  defmodule W do
    @moduledoc "W-type."
    defstruct [:name, :domain, :codomain]
  end

  defmodule Sup do
    @moduledoc "sup term (W-type constructor)."
    defstruct [:a, :b]
  end

  defmodule IndW do
    @moduledoc "IndW eliminator."
    defstruct [:a, :b, :motive]
  end

  # --- Pretty Printing ---

  @doc "Converts an AST term to its string representation."
  def to_string(term) do
    case term do
      %Var{name: name} ->
        name

      %Universe{level: l} ->
        "U#{int_to_subscript(l)}"

      %Pi{name: x, domain: a, codomain: b} ->
        domain_str = if complex?(a), do: "(#{to_string(a)})", else: to_string(a)
        "(#{x} : #{domain_str}) -> #{to_string(b)}"

      %Lam{name: x, body: b} ->
        "\\#{x} -> #{to_string(b)}"

      %App{func: f, arg: a} ->
        f_str = if binds_tightly?(f), do: to_string(f), else: "(#{to_string(f)})"
        a_str = if complex?(a), do: "(#{to_string(a)})", else: to_string(a)
        "#{f_str} #{a_str}"

      %Sigma{name: x, domain: a, codomain: b} ->
        domain_str = if complex?(a), do: "(#{to_string(a)})", else: to_string(a)
        "(#{x} : #{domain_str}) * #{to_string(b)}"

      %Pair{first: a, second: b} ->
        "(#{to_string(a)}, #{to_string(b)})"

      %Fst{expr: e} -> "#{to_string(e)}.1"
      %Snd{expr: e} -> "#{to_string(e)}.2"

      %Id{type: a} -> "Id #{to_string(a)}"
      %Refl{expr: e} -> "refl #{to_string(e)}"

      %PathP{path: p, u0: nil} -> "PathP #{to_string(p)}"
      %PathP{path: p, u0: u0, u1: nil} -> "PathP #{to_string(p)} #{to_string(u0)}"
      %PathP{path: p, u0: u0, u1: u1} -> "PathP #{to_string(p)} #{to_string(u0)} #{to_string(u1)}"
      %PLam{name: x, body: b} -> "<#{x}> #{to_string(b)}"

      %Interval{} -> "I"
      %Dir{val: d} -> "#{d}"

      %AppFormula{left: e, right: x} -> "#{to_string(e)} #{to_string(x)}"

      %Transp{path: p, phi: i} -> "transp #{to_string(p)} #{to_string(i)}"
      %HComp{type: t, phi: r, u: u, u0: u0} ->
        "hcomp #{to_string(t)} #{to_string(r)} #{to_string(u)} #{to_string(u0)}"

      %Partial{expr: e} -> "Partial #{to_string(e)}"
      %PartialP{type: t, phi: r} -> "PartialP #{to_string(t)} #{to_string(r)}"

      %System{map: m} ->
        m_str = Enum.map_join(m, ", ", fn {f, e} -> "#{inspect(f)} -> #{to_string(e)}" end)
        "[#{m_str}]"

      %Sub{type: a, phi: i, u: u} -> "Sub #{to_string(a)} #{to_string(i)} #{to_string(u)}"
      %Inc{type: t, phi: r} -> "inc #{to_string(t)} #{to_string(r)}"
      %Ouc{expr: e} -> "ouc #{to_string(e)}"

      %Neutral{term: t} ->
        to_string(t)

      %Empty{} -> "𝟎"
      %Unit{} -> "𝟏"
      %Star{} -> "★"
      %Bool{} -> "𝟐"
      %FalseConstant{} -> "0₂"
      %TrueConstant{} -> "1₂"

      %W{name: x, domain: a, codomain: b} ->
        domain_str = if complex?(a), do: "(#{to_string(a)})", else: to_string(a)
        "W(#{x} : #{domain_str}) #{to_string(b)}"
      %Sup{a: a, b: b} -> "sup #{to_string(a)} #{to_string(b)}"
      %IndW{a: a, b: b, motive: m} -> "indᵂ #{to_string(a)} #{to_string(b)} #{to_string(m)}"
      %IndEmpty{type: t} -> "ind₀ #{to_string(t)}"
      %IndUnit{type: t} -> "ind₁ #{to_string(t)}"
      %IndBool{type: t} -> "ind₂ #{to_string(t)}"

      nil -> "nil"

      _ ->
        inspect(term)
    end
  end

  defp complex?(%App{}), do: true
  defp complex?(%Lam{}), do: true
  defp complex?(%Pi{}), do: true
  defp complex?(%Sigma{}), do: true
  defp complex?(%W{}), do: true
  defp complex?(%Transp{}), do: true
  defp complex?(%HComp{}), do: true
  defp complex?(_), do: false

  # App func only needs parens if it's a binder or complex operator
  defp binds_tightly?(%Var{}), do: true
  defp binds_tightly?(%App{}), do: true
  defp binds_tightly?(_), do: false

  # --- Type/Term Utilities ---

  @doc "Creates a Pi type."
  def pi(name, domain, codomain), do: %Pi{name: name, domain: domain, codomain: codomain}
  @doc "Creates a non-dependent function type (arrow)."
  def arrow(a, b), do: %Pi{name: "_", domain: a, codomain: b}
  @doc "Creates a universe type."
  def universe(i), do: %Universe{level: i}
  @doc "Convenience for Nat variable."
  def nat(), do: %Var{name: "Nat"}
  @doc "Convenience for Bool variable."
  def bool(), do: %Var{name: "Bool"}
  @doc "Convenience for Unit variable."
  def unit(), do: %Var{name: "Unit"}

  defp int_to_subscript(n) do
    n
    |> Integer.to_string()
    |> String.graphemes()
    |> Enum.map(fn
      "0" -> "₀"
      "1" -> "₁"
      "2" -> "₂"
      "3" -> "₃"
      "4" -> "₄"
      "5" -> "₅"
      "6" -> "₆"
      "7" -> "₇"
      "8" -> "₈"
      "9" -> "₉"
      x -> x
    end)
    |> Enum.join()
  end

  @doc "Collects all dimension atoms (variable names) from a formula."
  def collect_atoms(expr) do
    do_collect_atoms(expr, MapSet.new())
    |> MapSet.to_list()
    |> Enum.sort()
  end

  defp do_collect_atoms(expr, acc) do
    case expr do
      %Var{name: n} -> MapSet.put(acc, n)
      %Neg{expr: e} -> do_collect_atoms(e, acc)
      %And{left: l, right: r} -> 
        acc = do_collect_atoms(l, acc)
        do_collect_atoms(r, acc)
      %Or{left: l, right: r} ->
        acc = do_collect_atoms(l, acc)
        do_collect_atoms(r, acc)
      %Neutral{term: t} -> do_collect_atoms(t, acc)
      _ -> acc
    end
  end
end
