defmodule Per.AST do
  import Kernel, except: [to_string: 1]

  @moduledoc """
  Abstract Syntax Tree structures for the Per compiler.
  """

  # --- Surface Language Declarations ---

  defmodule Neutral do
    defstruct [:term, :type]
  end

  defmodule Module do
    defstruct [:name, :declarations]
  end

  defmodule DeclValue do
    defstruct [:name, :type, :expr, :guards, :where_decls]
  end

  defmodule DeclTypeSignature do
    defstruct [:name, :type]
  end

  defmodule DeclForeign do
    defstruct [:name, :type, :erl_mod, :erl_func]
  end

  # --- Core Language Terms ---

  defmodule Var do
    defstruct [:name]
  end

  defmodule Universe do
    defstruct [:level]
  end

  defmodule Pi do
    defstruct [:name, :domain, :codomain]
  end

  defmodule Lam do
    defstruct [:name, :domain, :body]
  end

  defmodule App do
    defstruct [:func, :arg]
  end

  defmodule Hole do
    defstruct []
  end

  defmodule Sigma do
    defstruct [:name, :domain, :codomain]
  end

  defmodule Pair do
    defstruct [:first, :second, tag: nil]
  end

  defmodule Fst do
    defstruct [:expr]
  end

  defmodule Snd do
    defstruct [:expr]
  end

  defmodule Field do
    defstruct [:expr, :name]
  end

  defmodule Id do
    defstruct [:type]
  end

  defmodule Refl do
    defstruct [:expr]
  end

  defmodule IdJ do
    defstruct [:expr]
  end

  defmodule PathP do
    defstruct [:path, :u0, :u1]
  end

  defmodule PLam do
    defstruct [:name, :body]
  end

  defmodule AppFormula do
    defstruct [:left, :right]
  end

  defmodule Interval do
    defstruct []
  end

  defmodule Dir do
    defstruct [:val] # 0 or 1
  end

  defmodule And do
    defstruct [:left, :right]
  end

  defmodule Or do
    defstruct [:left, :right]
  end

  defmodule Neg do
    defstruct [:expr]
  end

  defmodule Transp do
    defstruct [:path, :phi]
  end

  defmodule HComp do
    defstruct [:type, :phi, :u, :u0]
  end

  defmodule Partial do
    defstruct [:expr]
  end

  defmodule PartialP do
    defstruct [:type, :phi]
  end

  defmodule System do
    defstruct [:map] # map of face -> expr
  end

  defmodule Sub do
    defstruct [:type, :phi, :u]
  end

  defmodule Inc do
    defstruct [:type, :phi]
  end

  defmodule Ouc do
    defstruct [:expr]
  end

  defmodule Empty do
    defstruct []
  end

  defmodule IndEmpty do
    defstruct [:type]
  end

  defmodule Unit do
    defstruct []
  end

  defmodule Star do
    defstruct []
  end

  defmodule IndUnit do
    defstruct [:type]
  end

  defmodule Bool do
    defstruct []
  end

  defmodule FalseConstant do
    defstruct []
  end

  defmodule TrueConstant do
    defstruct []
  end

  defmodule IndBool do
    defstruct [:type]
  end

  defmodule W do
    defstruct [:name, :domain, :codomain]
  end

  defmodule Sup do
    defstruct [:a, :b]
  end

  defmodule IndW do
    defstruct [:a, :b, :motive]
  end

  # --- Pretty Printing ---

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

      %Empty{} -> "Empty"
      %Unit{} -> "Unit"
      %Star{} -> "star"
      %Bool{} -> "Bool"
      %FalseConstant{} -> "false"
      %TrueConstant{} -> "true"

      %W{name: x, domain: a, codomain: b} ->
        domain_str = if complex?(a), do: "(#{to_string(a)})", else: to_string(a)
        "W(#{x} : #{domain_str}) #{to_string(b)}"
      %Sup{a: a, b: b} -> "sup #{to_string(a)} #{to_string(b)}"
      %IndW{a: a, b: b, motive: m} -> "indᵂ #{to_string(a)} #{to_string(b)} #{to_string(m)}"
      %IndEmpty{type: t} -> "ind₀ #{to_string(t)}"
      %IndUnit{type: t} -> "ind₁ #{to_string(t)}"
      %IndBool{type: t} -> "ind₂ #{to_string(t)}"

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

  def pi(name, domain, codomain), do: %Pi{name: name, domain: domain, codomain: codomain}
  def arrow(a, b), do: %Pi{name: "_", domain: a, codomain: b}
  def universe(i), do: %Universe{level: i}
  def nat(), do: %Var{name: "Nat"}
  def bool(), do: %Var{name: "Bool"}
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
end
