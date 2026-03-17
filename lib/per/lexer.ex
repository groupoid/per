defmodule Per.Lexer do
  @moduledoc """
  Lexer for Per (Lean-like syntax).
  """

  def lex(input) do
    lex(String.to_charlist(input), 1, 1, [])
  end

  defp lex([], _line, _col, acc), do: {:ok, Enum.reverse(acc)}

  defp lex([?\n | rest], line, _col, acc), do: lex(rest, line + 1, 1, acc)
  defp lex([?\s | rest], line, col, acc), do: lex(rest, line, col + 1, acc)
  defp lex([?\r | rest], line, col, acc), do: lex(rest, line, col, acc)
  defp lex([?\t | rest], line, col, acc), do: lex(rest, line, col + 4, acc)

  # Comments (PureScript/Haskell style --)
  defp lex([?-, ?- | rest], line, col, acc) do
    rest2 = Enum.drop_while(rest, fn c -> c != ?\n end)
    lex(rest2, line, col, acc)
  end

  # Multi-line comments {- ... -}
  defp lex([?{, ?- | rest], line, col, acc) do
    {rest2, new_line, new_col} = take_comment(rest, line, col + 2)
    lex(rest2, new_line, new_col, acc)
  end

  # Special symbols
  defp lex([?( | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:left_paren, line, col} | acc])

  defp lex([?) | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:right_paren, line, col} | acc])

  defp lex([?[ | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:left_square, line, col} | acc])

  defp lex([?] | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:right_square, line, col} | acc])

  defp lex([?{ | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:left_brace, line, col} | acc])

  defp lex([?} | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:right_brace, line, col} | acc])

  defp lex([?, | rest], line, col, acc), do: lex(rest, line, col + 1, [{:comma, line, col} | acc])

  defp lex([?; | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:semicolon, line, col} | acc])

  defp lex([?., ?. | rest], line, col, acc),
    do: lex(rest, line, col + 2, [{:dotdot, line, col} | acc])

  defp lex([?. | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:dot, line, col} | acc])

  # Arrow, Backslash, Lambda symbol
  defp lex([?-, ?> | rest], line, col, acc),
    do: lex(rest, line, col + 2, [{:arrow, line, col} | acc])

  # UTF-8 Symbols
  defp lex([0xE2, 0x86, 0x92 | rest], line, col, acc), # →
    do: lex(rest, line, col + 3, [{:arrow, line, col} | acc])

  defp lex([0xCE, 0xBB | rest], line, col, acc), # λ
    do: lex(rest, line, col + 2, [{:backslash, line, col} | acc])

  defp lex([0xCE, 0xA0 | rest], line, col, acc), # Π
    do: lex(rest, line, col + 2, [{:pi_token, line, col} | acc])

  defp lex([0xCE, 0xA3 | rest], line, col, acc), # Σ
    do: lex(rest, line, col + 2, [{:sigma_token, line, col} | acc])

  defp lex([0xE2, 0x88, 0xA7 | rest], line, col, acc), # ∧
    do: lex(rest, line, col + 3, [{:and_token, line, col} | acc])

  defp lex([0xE2, 0x88, 0xA8 | rest], line, col, acc), # ∨
    do: lex(rest, line, col + 3, [{:or_token, line, col} | acc])

  defp lex([?\\ | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:backslash, line, col} | acc])

  # Numbers
  defp lex([c | rest], line, col, acc) when c >= ?0 and c <= ?9 do
    {num_chars, rest2} = take_while([c | rest], fn x -> x >= ?0 and x <= ?9 end)
    num = List.to_integer(num_chars)
    lex(rest2, line, col + length(num_chars), [{:number, line, col, num} | acc])
  end

  # Identifiers and Keywords
  defp lex([c | rest], line, col, acc)
       when (c >= ?a and c <= ?z) or (c >= ?A and c <= ?Z) or c == ?_ or c > 127 do
    {ident_chars, rest2} = take_ident([c | rest])
    ident = List.to_string(ident_chars)

    case ident do
      "module" -> lex(rest2, line, col + String.length(ident), [{:module, line, col} | acc])
      "where" -> lex(rest2, line, col + String.length(ident), [{:where, line, col} | acc])
      "import" -> lex(rest2, line, col + String.length(ident), [{:import, line, col} | acc])
      "option" -> lex(rest2, line, col + String.length(ident), [{:option_kw, line, col} | acc])
      "inductive" -> lex(rest2, line, col + String.length(ident), [{:ident, line, col, ident} | acc])
      "data" -> lex(rest2, line, col + String.length(ident), [{:ident, line, col, ident} | acc])
      "def" -> lex(rest2, line, col + String.length(ident), [{:def_kw, line, col} | acc])
      "theorem" -> lex(rest2, line, col + String.length(ident), [{:def_kw, line, col} | acc])
      "axiom" -> lex(rest2, line, col + String.length(ident), [{:axiom_kw, line, col} | acc])
      "postulate" -> lex(rest2, line, col + String.length(ident), [{:axiom_kw, line, col} | acc])
      "let" -> lex(rest2, line, col + String.length(ident), [{:let, line, col} | acc])
      "in" -> lex(rest2, line, col + String.length(ident), [{:in, line, col} | acc])
      "if" -> lex(rest2, line, col + String.length(ident), [{:if_kw, line, col} | acc])
      "then" -> lex(rest2, line, col + String.length(ident), [{:then_kw, line, col} | acc])
      "else" -> lex(rest2, line, col + String.length(ident), [{:else_kw, line, col} | acc])
      "case" -> lex(rest2, line, col + String.length(ident), [{:ident, line, col, ident} | acc])
      "of" -> lex(rest2, line, col + String.length(ident), [{:ident, line, col, ident} | acc])
      "foreign" -> lex(rest2, line, col + String.length(ident), [{:foreign, line, col} | acc])
      "PathP" -> lex(rest2, line, col + String.length(ident), [{:pathp, line, col} | acc])
      "transp" -> lex(rest2, line, col + String.length(ident), [{:transp, line, col} | acc])
      "hcomp" -> lex(rest2, line, col + String.length(ident), [{:hcomp, line, col} | acc])
      "Partial" -> lex(rest2, line, col + String.length(ident), [{:partial, line, col} | acc])
      "PartialP" -> lex(rest2, line, col + String.length(ident), [{:partialp, line, col} | acc])
      "inc" -> lex(rest2, line, col + String.length(ident), [{:inc, line, col} | acc])
      "ouc" -> lex(rest2, line, col + String.length(ident), [{:ouc, line, col} | acc])
      "sup" -> lex(rest2, line, col + String.length(ident), [{:sup, line, col} | acc])
      "W" -> lex(rest2, line, col + String.length(ident), [{:w_type, line, col} | acc])
      "Id" -> lex(rest2, line, col + String.length(ident), [{:id_type, line, col} | acc])
      "ref" -> lex(rest2, line, col + String.length(ident), [{:ref_term, line, col} | acc])
      "idJ" -> lex(rest2, line, col + String.length(ident), [{:idj, line, col} | acc])
      "ind-empty" -> lex(rest2, line, col + String.length(ident), [{:ind_empty, line, col} | acc])
      "ind-unit" -> lex(rest2, line, col + String.length(ident), [{:ind_unit, line, col} | acc])
      "ind-bool" -> lex(rest2, line, col + String.length(ident), [{:ind_bool, line, col} | acc])
      "ind-W" -> lex(rest2, line, col + String.length(ident), [{:ind_w, line, col} | acc])
      "𝟎" -> lex(rest2, line, col + String.length(ident), [{:empty_type, line, col} | acc])
      "𝟏" -> lex(rest2, line, col + String.length(ident), [{:unit_type, line, col} | acc])
      "𝟐" -> lex(rest2, line, col + String.length(ident), [{:bool_type, line, col} | acc])
      "ind₀" -> lex(rest2, line, col + String.length(ident), [{:ind_empty, line, col} | acc])
      "ind₁" -> lex(rest2, line, col + String.length(ident), [{:ind_unit, line, col} | acc])
      "ind₂" -> lex(rest2, line, col + String.length(ident), [{:ind_bool, line, col} | acc])
      "indᵂ" -> lex(rest2, line, col + String.length(ident), [{:ind_w, line, col} | acc])
      "false" -> lex(rest2, line, col + String.length(ident), [{:false_kw, line, col} | acc])
      "true" -> lex(rest2, line, col + String.length(ident), [{:true_kw, line, col} | acc])
      "0₂" -> lex(rest2, line, col + String.length(ident), [{:false_kw, line, col} | acc])
      "1₂" -> lex(rest2, line, col + String.length(ident), [{:true_kw, line, col} | acc])
      "star" -> lex(rest2, line, col + String.length(ident), [{:star_kw, line, col} | acc])
      "★" -> lex(rest2, line, col + String.length(ident), [{:star_kw, line, col} | acc])
      "Empty" -> lex(rest2, line, col + String.length(ident), [{:empty_type, line, col} | acc])
      "Unit" -> lex(rest2, line, col + String.length(ident), [{:unit_type, line, col} | acc])
      "Bool" -> lex(rest2, line, col + String.length(ident), [{:bool_type, line, col} | acc])
      "summa" -> lex(rest2, line, col + String.length(ident), [{:sigma_token, line, col} | acc])
      _ ->
        if String.starts_with?(ident, "U") and String.length(ident) > 1 and is_subscript?(String.at(ident, 1)) do
          level = subscript_to_int(String.slice(ident, 1..-1//1))
          lex(rest2, line, col + String.length(ident), [{:number, line, col, level} | acc])
        else
          lex(rest2, line, col + String.length(ident), [{:ident, line, col, ident} | acc])
        end
    end
  end

  # Operators
  defp lex([c | rest], line, col, acc)
       when c in [?=, ?|, ?:, ?<, ?>, ?+, ?-, ?*, ?/, ?%, ?^, ?&, ?!, ?$, ?#, ?@, ??] do
    {op_chars, rest2} =
      take_while([c | rest], fn x ->
        x in [?=, ?|, ?:, ?<, ?>, ?+, ?-, ?*, ?/, ?%, ?^, ?&, ?!, ?$, ?#, ?@, ??]
      end)

    op = List.to_string(op_chars)

    token =
      case op do
        "=" -> {:=, line, col}
        "|->" -> {:map, line, col}
        "|" -> {:pipe, line, col}
        ":=" -> {:defeq, line, col}
        ":" -> {:colon, line, col}
        "?" -> {:hole, line, col}
        "@" -> {:appformula, line, col}
        "/\\" -> {:and_token, line, col}
        "\\/" -> {:or_token, line, col}
        _ -> {:operator, line, col, op}
      end

    lex(rest2, line, col + String.length(op), [token | acc])
  end

  # Strings
  defp lex([?" | rest], line, col, acc) do
    {str_chars, rest2} = take_string(rest)

    lex(rest2, line, col + length(str_chars) + 2, [
      {:string, line, col, List.to_string(str_chars)} | acc
    ])
  end

  defp lex([c | _rest], line, col, _acc) do
    {:error, "Unexpected character: #{<<c::utf8>>} at #{line}:#{col}"}
  end

  defp take_ident([c | rest])
       when (c >= ?a and c <= ?z) or (c >= ?A and c <= ?Z) or (c >= ?0 and c <= ?9) or c == ?_ or
              c == ?' or c > 127 do
    {rest_ident, rest2} = take_ident(rest)
    {[c | rest_ident], rest2}
  end

  defp take_ident(rest), do: {[], rest}

  defp take_while([], _), do: {[], []}

  defp take_while([c | rest], f) do
    if f.(c) do
      {matched, remaining} = take_while(rest, f)
      {[c | matched], remaining}
    else
      {[], [c | rest]}
    end
  end

  defp take_string([?" | rest]), do: {[], rest}

  defp take_string([?\\, c | rest]) do
    {s, r} = take_string(rest)
    {[?\\, c | s], r}
  end

  defp take_string([c | rest]) do
    {s, r} = take_string(rest)
    {[c | s], r}
  end

  defp take_string([]), do: {[], []}

  defp is_subscript?(nil), do: false
  defp is_subscript?(c), do: c in ["₀", "₁", "₂", "₃", "₄", "₅", "₆", "₇", "₈", "₉"]

  defp subscript_to_int(s) do
    s
    |> String.graphemes()
    |> Enum.map(fn
      "₀" -> "0"
      "₁" -> "1"
      "₂" -> "2"
      "₃" -> "3"
      "₄" -> "4"
      "₅" -> "5"
      "₆" -> "6"
      "₇" -> "7"
      "₈" -> "8"
      "₉" -> "9"
      x -> x
    end)
    |> Enum.join()
    |> String.to_integer()
  end

  defp take_comment([?-, ?} | rest], line, col), do: {rest, line, col + 2}
  defp take_comment([?\n | rest], line, _col), do: take_comment(rest, line + 1, 1)
  defp take_comment([_c | rest], line, col), do: take_comment(rest, line, col + 1)
  defp take_comment([], line, col), do: {[], line, col}
end
