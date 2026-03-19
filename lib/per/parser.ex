defmodule Per.Parser do
  alias Per.AST

  def parse(tokens) when is_list(tokens) do
    # Strip explicit newlines and virtual semicolons, Layout has already handled block structure
    tokens = Enum.filter(tokens, fn t -> elem(t, 0) not in [:newline, :v_semicolon] end)
    parse_module(tokens)
  end

  def parse({:error, _} = err), do: err

  def parse_expression(tokens) do
    parse_expr(tokens)
  end

  def parse_declaration(tokens) do
    parse_decl(tokens)
  end

  defp parse_module(tokens) do
    # Skip any leading virtual tokens
    tokens = Enum.drop_while(tokens, fn t -> elem(t, 0) == :v_left_brace end)

    case tokens do
      [{:module, _, _} | rest] ->
        case parse_module_name(rest) do
          {:ok, name, [{:where, _, _} | rest2]} ->
            # Skip optional v_left_brace after where
            rest3 = Enum.drop_while(rest2, fn t -> elem(t, 0) == :v_left_brace end)

            case parse_decls(rest3, []) do
              {:ok, decls, remaining} ->
                {:ok, %AST.Module{name: name, declarations: decls}, remaining}

              {:error, _} = err ->
                err

              {:error, _, _} = err ->
                err
            end

          _ ->
            {:error, {:invalid_module_header, Enum.take(rest, 5)}}
        end

      _ ->
        case parse_decls(tokens, []) do
          {:ok, decls, remaining} -> {:ok, %AST.Module{name: "main", declarations: decls}, remaining}
          err -> err
        end
    end
  end

  defp parse_module_name([{:ident, _, _, name} | rest]) do
    parse_module_name_tail(rest, name)
  end

  defp parse_module_name_tail([{:dot, _, _}, {:ident, _, _, next} | rest], acc) do
    parse_module_name_tail(rest, acc <> "." <> next)
  end

  defp parse_module_name_tail([{:operator, _, _, "/"}, {:ident, _, _, next} | rest], acc) do
    parse_module_name_tail(rest, acc <> "/" <> next)
  end

  defp parse_module_name_tail([{:operator, _, _, "/"} | rest], acc) do
    parse_module_name_tail(rest, acc <> "/")
  end

  defp parse_module_name_tail(rest, acc), do: {:ok, acc, rest}

  defp parse_decls([], acc), do: {:ok, Enum.reverse(acc), []}
  defp parse_decls([{:v_left_brace, _, _} | rest], acc), do: parse_decls(rest, acc)
  defp parse_decls([{:v_right_brace, _, _} | rest], acc), do: {:ok, Enum.reverse(acc), rest}
  defp parse_decls([{:v_semicolon, _, _} | rest], acc), do: parse_decls(rest, acc)

  defp parse_decls(tokens, acc) do
    # Proactively skip semicolons before parse_decl
    tokens = Enum.drop_while(tokens, fn t -> elem(t, 0) == :v_semicolon or elem(t, 0) == :semicolon end)

    if tokens == [] or elem(hd(tokens), 0) == :v_right_brace do
      {:ok, Enum.reverse(acc), tokens}
    else
      case parse_decl(tokens) do
        {:ok, decl, rest} -> parse_decls(rest, [decl | acc])
        err when elem(err, 0) == :error -> err
      end
    end
  end

  defp parse_decl(tokens) do
    case tokens do
      [{:import, _, _} | rest] ->
        case parse_module_name(rest) do
          {:ok, name, rest2} -> {:ok, {:import, name}, rest2}
          _ -> {:error, :invalid_import}
        end
      [{:option_kw, _, _} | rest] ->
        case rest do
          [{:ident, _, _, name}, {:true_kw, _, _} | rest2] -> {:ok, {:option, name, true}, rest2}
          [{:ident, _, _, name}, {:false_kw, _, _} | rest2] -> {:ok, {:option, name, false}, rest2}
          _ -> {:error, :invalid_option}
        end
      [{:def_kw, _, _} | rest] -> parse_val_decl(rest)
      [{:axiom_kw, _, _} | rest] -> parse_axiom_decl(rest)
      [token | _rest] when elem(token, 0) in [:ident, :operator, :pi_token, :sigma_token, :prod_token] ->
        case parse_val_decl(tokens) do
          {:ok, _, _} = res -> res
          _ ->
            case parse_type_sig(tokens) do
              {:ok, _, _} = res -> res
              _ -> {:error, :unrecognized_decl}
            end
        end
      [token | rest] -> {:error, :invalid_declaration, [token | Enum.take(rest, 5)]}
      [] -> {:error, :unexpected_eof}
    end
  end

  defp parse_val_decl([token | rest] = _tokens) when elem(token, 0) in [:ident, :operator, :pi_token, :sigma_token, :prod_token] do
    name = extract_name(token)
    case parse_params(rest, []) do
      {:ok, params, [{:colon, _, _} | rest2]} ->
        case parse_expr(rest2) do
          {:ok, ty, [{:defeq, _, _} | rest3]} ->
             case parse_expr(rest3) do
               {:ok, expr, rest4} ->
                 # Desugar parameters
                 full_ty = mk_pi_tele(params, ty)
                 full_expr = mk_lam_tele(params, expr)
                 {:ok, %AST.DeclValue{name: name, type: full_ty, expr: full_expr}, rest4}
               err -> err
             end
           _ -> {:error, :expected_defeq}
        end
      {:ok, params, [divider | rest2]} when elem(divider, 0) in [:defeq, :=] ->
        case parse_expr(rest2) do
          {:ok, expr, rest3} ->
            full_expr = mk_lam_tele(params, expr)
            {:ok, %AST.DeclValue{name: name, type: %AST.Hole{}, expr: full_expr}, rest3}
          err -> err
        end
      err ->
        err
    end
  end

  defp parse_axiom_decl([{:ident, _, _, name} | rest]) do
    case parse_params(rest, []) do
      {:ok, params, [{:colon, _, _} | rest2]} ->
        case parse_expr(rest2) do
          {:ok, ty, rest3} ->
            full_ty = mk_pi_tele(params, ty)
            {:ok, %AST.DeclTypeSignature{name: name, type: full_ty}, rest3}
          err -> err
        end
      _ -> {:error, :invalid_axiom_decl}
    end
  end

  defp parse_type_sig([token, {:colon, _, _} | rest]) when elem(token, 0) in [:ident, :operator, :pi_token, :sigma_token, :prod_token] do
    name = extract_name(token)
    case parse_expr(rest) do
      {:ok, ty, rest2} -> {:ok, %AST.DeclTypeSignature{name: name, type: ty}, rest2}
      err -> err
    end
  end

  defp parse_params(tokens, acc) do
    case tokens do
      [{:left_paren, _, _} | _] ->
        case parse_lense(tokens) do
          {:ok, params, rest} -> parse_params(rest, acc ++ params)
          _ -> {:ok, acc, tokens}
        end
      _ -> {:ok, acc, tokens}
    end
  end

  defp parse_lense([{:left_paren, _, _} | rest]) do
    case parse_vars(rest) do
      {:ok, vars, [{:colon, _, _} | rest2]} ->
        case parse_expr(rest2) do
          {:ok, ty, [{:right_paren, _, _} | rest3]} ->
            {:ok, Enum.map(vars, fn v -> {v, ty} end), rest3}
          _ -> {:error, :invalid_lense_type}
        end
      _ -> {:error, :invalid_lense}
    end
  end


  defp parse_expr(tokens), do: parse_expr_binder(tokens)

  defp parse_expr_binder([{:backslash, _, _} | rest]), do: parse_lam(rest)
  defp parse_expr_binder([{:pi_token, _, _, _} | rest] = tokens) do
    case parse_pi(rest) do
      {:ok, e, rest2} -> {:ok, e, rest2}
      _ -> parse_expr_logic_or(tokens)
    end
  end
  defp parse_expr_binder([{:sigma_token, _, _, _} | rest] = tokens) do
    case parse_sigma(rest) do
      {:ok, e, rest2} -> {:ok, e, rest2}
      _ -> parse_expr_logic_or(tokens)
    end
  end
  defp parse_expr_binder([{:w_type, _, _} | rest]), do: parse_w(rest)
  defp parse_expr_binder(tokens), do: parse_expr_logic_arrow(tokens)

  defp parse_lam(rest) do
    case parse_params(rest, []) do
      {:ok, params, [divider | rest2]} when elem(divider, 0) in [:arrow, :comma] ->
        case parse_expr(rest2) do
          {:ok, body, rest3} ->
            {:ok, mk_lam_tele(params, body), rest3}
          err -> err
        end
      _ -> {:error, :invalid_lambda}
    end
  end

  defp parse_pi(rest) do
    case parse_params(rest, []) do
      {:ok, params, [divider | rest2]} when elem(divider, 0) in [:arrow, :comma] ->
        case parse_expr(rest2) do
          {:ok, body, rest3} ->
            {:ok, mk_pi_tele(params, body), rest3}
          err -> err
        end
      _ -> {:error, :invalid_pi}
    end
  end

  defp parse_sigma(rest) do
    case parse_params(rest, []) do
      {:ok, [], rest2} -> {:error, :not_a_binder, rest2}
      {:ok, params, [divider | rest2]} when elem(divider, 0) in [:prod_token, :comma] ->
        case parse_expr(rest2) do
          {:ok, body, rest3} -> {:ok, mk_sigma_tele(params, body), rest3}
          err -> err
        end
      {:ok, _params, rest2} ->
        {:error, :expected_sigma_divider, rest2}
      err ->
        err
    end
  end

  defp parse_w(rest) do
    # W (x : A), B x
    case rest do
      [{:left_paren, _, _}, {:ident, _, _, name}, {:colon, _, _} | rest2] ->
        case parse_expr(rest2) do
          {:ok, a, [{:right_paren, _, _}, {:comma, _, _} | rest3]} ->
            case parse_expr(rest3) do
              {:ok, b, rest4} -> {:ok, %AST.W{name: name, domain: a, codomain: b}, rest4}
              err -> err
            end
          err -> err
        end
      _ -> {:error, :invalid_w_type}
    end
  end

  defp parse_expr_logic_or(tokens) do
    case parse_expr_logic_and(tokens) do
      {:ok, e1, [{:or_token, _, _} | rest]} ->
        case parse_expr_logic_or(rest) do
          {:ok, e2, rest2} -> {:ok, %AST.Or{left: e1, right: e2}, rest2}
          _ -> {:ok, e1, rest}
        end
      res -> res
    end
  end

  defp parse_expr_logic_and(tokens) do
    case parse_expr_app(tokens) do
      {:ok, e1, [{:and_token, _, _} | rest]} ->
        case parse_expr_logic_and(rest) do
          {:ok, e2, rest2} -> {:ok, %AST.And{left: e1, right: e2}, rest2}
          _ -> {:ok, e1, rest}
        end
      res -> res
    end
  end

  defp parse_expr_logic_arrow(tokens) do
    case parse_expr_logic_at(tokens) do
      {:ok, e1, [{:arrow, _, _} | rest]} ->
        case parse_expr_logic_arrow(rest) do
          {:ok, e2, rest2} -> {:ok, %AST.Pi{name: "_", domain: e1, codomain: e2}, rest2}
          _ -> {:ok, e1, rest}
        end
      {:ok, e1, [{:prod_token, _, _} | rest]} ->
        case parse_expr_logic_arrow(rest) do
          {:ok, e2, rest2} -> {:ok, %AST.Sigma{name: "_", domain: e1, codomain: e2}, rest2}
          _ -> {:ok, e1, rest}
        end
      res -> res
    end
  end

  defp parse_expr_logic_at(tokens) do
    case parse_expr_logic_or(tokens) do
      {:ok, e1, rest} -> parse_expr_logic_at_tail(e1, rest)
      err -> err
    end
  end

  defp parse_expr_logic_at_tail(e1, [{:at_sign, _, _} | rest]) do
    case parse_expr_logic_or(rest) do
      {:ok, e2, rest2} -> parse_expr_logic_at_tail(%AST.AppFormula{left: e1, right: e2}, rest2)
      err -> err
    end
  end
  defp parse_expr_logic_at_tail(e1, rest), do: {:ok, e1, rest}

  defp parse_expr_app(tokens) do
    case parse_expr_unary(tokens) do
      {:ok, f, rest} -> parse_expr_app_tail(f, rest)
      err -> err
    end
  end


  defp parse_expr_unary(tokens) do
    case do_parse_expr_unary(tokens) do
      {:ok, f, rest} -> parse_expr_unary_tail(f, rest)
      err -> err
    end
  end

  defp parse_expr_unary_tail(f, tokens) do
    case tokens do
      [{:dot, _, _}, {:number, _, _, 1} | rest] -> parse_expr_unary_tail(%AST.Fst{expr: f}, rest)
      [{:dot, _, _}, {:number, _, _, 2} | rest] -> parse_expr_unary_tail(%AST.Snd{expr: f}, rest)
      [{:dot, _, _}, {:ident, _, _, name} | rest] -> parse_expr_unary_tail(%AST.Field{expr: f, name: name}, rest)
      _ -> {:ok, f, tokens}
    end
  end

  defp do_parse_expr_unary([]), do: {:error, :unexpected_eof}
  defp do_parse_expr_unary([token | rest] = tokens) do
    case token do
      {:pathp, _, _} ->
        case parse_expr_unary(rest) do
          {:ok, p, rest2} -> {:ok, %AST.PathP{path: p}, rest2}
          err -> err
        end
      {:transp, _, _} ->
        case parse_expr_unary(rest) do
          {:ok, p, rest2} ->
            case parse_expr_unary(rest2) do
              {:ok, phi, rest3} -> {:ok, %AST.Transp{path: p, phi: phi}, rest3}
              err -> err
            end
          err -> err
        end
      {:hcomp, _, _} ->
        case parse_expr_unary(rest) do
          {:ok, t, rest2} ->
            case parse_expr_unary(rest2) do
              {:ok, phi, rest3} ->
                case parse_expr_unary(rest3) do
                  {:ok, u, rest4} ->
                    case parse_expr_unary(rest4) do
                      {:ok, u0, rest5} -> {:ok, %AST.HComp{type: t, phi: phi, u: u, u0: u0}, rest5}
                      err -> err
                    end
                  err -> err
                end
              err -> err
            end
          err -> err
        end
      {:partial, _, _} ->
        case parse_expr_unary(rest) do
          {:ok, e, rest2} -> {:ok, %AST.Partial{expr: e}, rest2}
          err -> err
        end
      {:partialp, _, _} ->
        case parse_expr_unary(rest) do
          {:ok, t, rest2} ->
            case parse_expr_unary(rest2) do
              {:ok, phi, rest3} -> {:ok, %AST.PartialP{type: t, phi: phi}, rest3}
              err -> err
            end
          err -> err
        end
      {:sup, _, _} ->
        case parse_expr_unary(rest) do
          {:ok, a, rest2} ->
            case parse_expr_unary(rest2) do
              {:ok, b, rest3} -> {:ok, %AST.Sup{a: a, b: b}, rest3}
              err -> err
            end
          err -> err
        end
      {:ind_w, _, _} ->
        case parse_expr_unary(rest) do
          {:ok, a, rest2} ->
            case parse_expr_unary(rest2) do
              {:ok, b, rest3} ->
                case parse_expr_unary(rest3) do
                  {:ok, c, rest4} -> {:ok, %AST.IndW{a: a, b: b, motive: c}, rest4}
                  err -> err
                end
              err -> err
            end
          err -> err
        end
      {:id_type, _, _} ->
        case parse_expr_unary(rest) do
          {:ok, t, rest2} -> {:ok, %AST.Id{type: t}, rest2}
          err -> err
        end
      {:ref_term, _, _} ->
        case parse_expr_unary(rest) do
          {:ok, e, rest2} -> {:ok, %AST.Refl{expr: e}, rest2}
          err -> err
        end
      {:idj, _, _} ->
        case parse_expr_unary(rest) do
          {:ok, e, rest2} -> {:ok, %AST.IdJ{expr: e}, rest2}
          err -> err
        end
      {:ind_empty, _, _} ->
        case parse_expr_unary(rest) do
          {:ok, t, rest2} -> {:ok, %AST.IndEmpty{type: t}, rest2}
          err -> err
        end
      {:ind_unit, _, _} ->
        case parse_expr_unary(rest) do
          {:ok, t, rest2} -> {:ok, %AST.IndUnit{type: t}, rest2}
          err -> err
        end
      {:ind_bool, _, _} ->
        case parse_expr_unary(rest) do
          {:ok, t, rest2} -> {:ok, %AST.IndBool{type: t}, rest2}
          err -> err
        end
      {:operator, _, _, "-"} ->
        case parse_expr_unary(rest) do
          {:ok, e, rest2} -> {:ok, %AST.Neg{expr: e}, rest2}
          err -> err
        end
      _ -> parse_expr_atom(tokens)
    end
  end

  defp parse_expr_atom([token | rest]) do
    case token do
      {:number, _, _, 0} -> {:ok, %AST.Dir{val: 0}, rest}
      {:number, _, _, 1} -> {:ok, %AST.Dir{val: 1}, rest}
      {:ident, _, _, "0"} -> {:ok, %AST.Dir{val: 0}, rest}
      {:ident, _, _, "1"} -> {:ok, %AST.Dir{val: 1}, rest}
      {:ident, _, _, name} -> {:ok, %AST.Var{name: name}, rest}
      {:operator, _, _, name} -> {:ok, %AST.Var{name: name}, rest}
      {:universe_token, _, _, val} -> {:ok, %AST.Universe{level: val}, rest}
      {:number, _, _, val} -> {:ok, %AST.Universe{level: val}, rest}
      {:hole, _, _} -> {:ok, %AST.Hole{}, rest}
      {:left_angle, _, _} ->
        case parse_vars(rest) do
          {:ok, vars, [{:right_angle, _, _} | rest2]} ->
            case parse_expr(rest2) do
              {:ok, body, rest3} ->
                {:ok, desugar_path_lam(vars, body), rest3}
              err -> err
            end
          _ -> {:error, :invalid_path_lambda}
        end
      {:left_paren, _, _} ->
        case parse_expr_list(rest, []) do
          {:ok, exprs, [{:right_paren, _, _} | rest2]} ->
            case exprs do
              [e] -> {:ok, e, rest2}
              _ -> {:ok, mk_nested_pair(exprs), rest2}
            end
          err -> err
        end
      {:left_square, _, _} ->
        case parse_system(rest, []) do
          {:ok, sys, [{:right_square, _, _} | rest2]} -> {:ok, %AST.System{map: sys}, rest2}
          err -> err
        end
      {:empty_type, _, _} -> {:ok, %AST.Empty{}, rest}
      {:unit_type, _, _} -> {:ok, %AST.Unit{}, rest}
      {:bool_type, _, _} -> {:ok, %AST.Bool{}, rest}
      {:false_kw, _, _} -> {:ok, %AST.FalseConstant{}, rest}
      {:true_kw, _, _} -> {:ok, %AST.TrueConstant{}, rest}
      {:star_kw, _, _} -> {:ok, %AST.Star{}, rest}
      {:interval_token, _, _} -> {:ok, %AST.Interval{}, rest}
      _ -> {:error, :no_expr_atom, token}
    end
  end

  defp mk_nested_pair([e]), do: e
  defp mk_nested_pair([h | t]), do: %AST.Pair{first: h, second: mk_nested_pair(t)}

  defp parse_expr_list(tokens, acc) do
    case parse_expr(tokens) do
      {:ok, e, [{:comma, _, _} | rest]} -> parse_expr_list(rest, [e | acc])
      {:ok, e, rest} -> {:ok, Enum.reverse([e | acc]), rest}
      _ -> {:ok, Enum.reverse(acc), tokens}
    end
  end

  defp parse_system(tokens, acc) do
     case tokens do
       [{:right_square, _, _} | _] -> {:ok, Enum.reverse(acc), tokens}
       _ ->
         case parse_face(tokens) do
           {:ok, face, [{:arrow, _, _} | rest]} ->
             case parse_expr(rest) do
               {:ok, e, rest2} ->
                 case rest2 do
                   [{:comma, _, _} | rest3] -> parse_system(rest3, [{face, e} | acc])
                   _ -> {:ok, Enum.reverse([{face, e} | acc]), rest2}
                 end
               err -> err
             end
           _ -> {:ok, Enum.reverse(acc), tokens}
         end
     end
  end

  defp parse_face(tokens) do
    case tokens do
      [{:left_paren, _, _}, {:ident, _, _, p}, divider, {:number, _, _, d}, {:right_paren, _, _} | rest]
      when (elem(divider, 0) == :defeq) or (elem(divider, 0) == :=) or (elem(divider, 0) == :operator and elem(divider, 3) == "=") ->
        {:ok, {p, d}, rest}
      _ -> {:error, :invalid_face}
    end
  end

  defp parse_expr_app_tail(f, tokens) do
    case parse_expr_unary(tokens) do
      {:ok, arg, rest} -> parse_expr_app_tail(%AST.App{func: f, arg: arg}, rest)
      _ -> {:ok, f, tokens}
    end
  end

  defp parse_vars([token | rest]) when elem(token, 0) in [:ident, :operator, :hole, :pi_token, :sigma_token] do
    name = extract_name(token)
    case parse_vars(rest) do
      {:ok, names, rest2} -> {:ok, [name | names], rest2}
      _ -> {:ok, [name], rest}
    end
  end
  defp parse_vars(tokens), do: {:ok, [], tokens}

  defp desugar_path_lam([], body), do: body
  defp desugar_path_lam([v | rest], body) do
    # EPLam (v, body)
    %AST.PLam{name: v, body: desugar_path_lam(rest, body)}
  end

  defp mk_pi_tele([], type), do: type
  defp mk_pi_tele([param | rest], type) do
    case param do
      {name, ty} -> %AST.Pi{name: name, domain: ty, codomain: mk_pi_tele(rest, type)}
      %AST.Var{name: name} -> %AST.Pi{name: name, domain: %AST.Hole{}, codomain: mk_pi_tele(rest, type)}
    end
  end

  defp mk_sigma_tele([], type), do: type
  defp mk_sigma_tele([param | rest], type) do
    case param do
      {name, ty} -> %AST.Sigma{name: name, domain: ty, codomain: mk_sigma_tele(rest, type)}
      %AST.Var{name: name} -> %AST.Sigma{name: name, domain: %AST.Hole{}, codomain: mk_sigma_tele(rest, type)}
    end
  end

  defp mk_lam_tele([], expr), do: expr
  defp mk_lam_tele([param | rest], expr) do
    case param do
      {name, ty} -> %AST.Lam{name: name, domain: ty, body: mk_lam_tele(rest, expr)}
      %AST.Var{name: name} -> %AST.Lam{name: name, domain: %AST.Hole{}, body: mk_lam_tele(rest, expr)}
    end
  end

  defp extract_name({:ident, _, _, name}), do: name
  defp extract_name({:operator, _, _, name}), do: name
  defp extract_name(token) when is_atom(elem(token, 0)), do: to_string(elem(token, 0))
end
