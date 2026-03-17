defmodule Per.Parser do
  alias Per.AST

  def parse(tokens) do
    parse_module(tokens)
  end

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
    IO.inspect(tokens, label: "PARSE_DECL_TOKENS", limit: :infinity)
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
      [{:ident, _, _, _name} | _rest] ->
        case parse_val_decl(tokens) do
          {:ok, _, _} = res -> res
          _ ->
            case parse_type_sig(tokens) do
              {:ok, _, _} = res -> res
              _ -> {:error, :unrecognized_decl}
            end
        end
      _ -> {:error, :invalid_declaration, Enum.take(tokens, 5)}
    end
  end

  defp parse_val_decl([{:ident, _, _, name} | rest]) do
    case parse_params(rest, []) do
      {:ok, params, [{:colon, _, _} | rest2]} ->
        case parse_type(rest2) do
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
      _ -> {:error, :invalid_val_decl}
    end
  end

  defp parse_axiom_decl([{:ident, _, _, name} | rest]) do
    case parse_params(rest, []) do
      {:ok, params, [{:colon, _, _} | rest2]} ->
        case parse_type(rest2) do
          {:ok, ty, rest3} ->
            full_ty = mk_pi_tele(params, ty)
            {:ok, %AST.DeclTypeSignature{name: name, type: full_ty}, rest3}
          err -> err
        end
      _ -> {:error, :invalid_axiom_decl}
    end
  end

  defp parse_type_sig([{:ident, _, _, name}, {:colon, _, _} | rest]) do
    case parse_type(rest) do
      {:ok, ty, rest2} -> {:ok, %AST.DeclTypeSignature{name: name, type: ty}, rest2}
      err -> err
    end
  end

  defp parse_params(tokens, acc) do
    case tokens do
      [{:ident, _, _, name} | rest] -> parse_params(rest, [%AST.Var{name: name} | acc])
      [{:left_paren, _, _}, {:ident, _, _, name}, {:colon, _, _} | rest] ->
         case parse_type(rest) do
           {:ok, ty, [{:right_paren, _, _} | rest2]} ->
             parse_params(rest2, [{name, ty} | acc])
           _ -> {:error, :invalid_param}
         end
      _ -> {:ok, Enum.reverse(acc), tokens}
    end
  end

  defp parse_type(tokens) do
    case parse_type_prod(tokens) do
      {:ok, t, [{:arrow, _, _} | rest]} ->
        case parse_type(rest) do
          {:ok, t2, rest2} -> {:ok, %AST.Pi{name: "_", domain: t, codomain: t2}, rest2}
          _ -> {:ok, t, rest}
        end
      res -> res
    end
  end

  defp parse_type_prod(tokens) do
    case parse_type_app(tokens) do
      {:ok, t1, [{:operator, _, _, "*"} | rest]} -> # Using * for Sigma for now if tokens don't have sigma_token
        case parse_type_prod(rest) do
          {:ok, t2, rest2} -> {:ok, %AST.Sigma{name: "_", domain: t1, codomain: t2}, rest2}
          _ -> {:ok, t1, rest}
        end
      {:ok, t1, [{:sigma_token, _, _} | rest]} ->
         case parse_type_prod(rest) do
           {:ok, t2, rest2} -> {:ok, %AST.Sigma{name: "_", domain: t1, codomain: t2}, rest2}
           _ -> {:ok, t1, rest}
         end
      res -> res
    end
  end

  defp parse_type_app(tokens) do
    case parse_type_atom(tokens) do
      {:ok, t, rest} -> parse_type_app_tail(t, rest)
      err -> err
    end
  end

  defp parse_type_app_tail(f, tokens) do
    case parse_type_atom(tokens) do
      {:ok, arg, rest} -> parse_type_app_tail(%AST.App{func: f, arg: arg}, rest)
      _ -> {:ok, f, tokens}
    end
  end

  defp parse_type_atom([{:ident, _, _, name} | rest]), do: {:ok, %AST.Var{name: name}, rest}
  defp parse_type_atom([{:number, _, _, val} | rest]), do: {:ok, %AST.Universe{level: val}, rest}

  defp parse_type_atom([{:left_paren, _, _}, {:ident, _, _, name}, {:colon, _, _} | rest]) do
    case parse_type(rest) do
      {:ok, t, [{:right_paren, _, _} | rest2]} ->
        {:ok, {name, t}, rest2}
      err -> err
    end
  end

  defp parse_type_atom([{:left_paren, _, _} | rest] = tokens) do
    case parse_expr(rest) do
      {:ok, e, [{:right_paren, _, _} | rest2]} -> {:ok, e, rest2}
      _ ->
        case parse_expr_atom(tokens) do
          {:ok, e, rest2} -> {:ok, e, rest2}
          err -> err
        end
    end
  end

  defp parse_type_atom(tokens) do
    case parse_expr_atom(tokens) do
      {:ok, e, rest} -> {:ok, e, rest}
      _ -> {:error, :no_type_atom, Enum.take(tokens, 5)}
    end
  end

  defp parse_binders([{:ident, _, _, name} | rest], acc),
    do: parse_binders(rest, [%AST.Var{name: name} | acc])

  defp parse_binders(tokens, acc), do: {:ok, Enum.reverse(acc), tokens}

  defp parse_expr(tokens) do
    case parse_expr_formula(tokens) do
      {:ok, f, rest} -> parse_expr_app_tail(f, rest)
      err -> err
    end
  end

  defp parse_expr_formula(tokens) do
    case parse_expr_atom(tokens) do
      {:ok, e1, [{:and_token, _, _} | rest]} ->
        case parse_expr_formula(rest) do
          {:ok, e2, rest2} -> {:ok, %AST.And{left: e1, right: e2}, rest2}
          _ -> {:ok, e1, rest}
        end
      {:ok, e1, [{:or_token, _, _} | rest]} ->
        case parse_expr_formula(rest) do
          {:ok, e2, rest2} -> {:ok, %AST.Or{left: e1, right: e2}, rest2}
          _ -> {:ok, e1, rest}
        end
      res -> res
    end
  end

  defp parse_expr_atom([{:ident, _, _, name} | rest]), do: {:ok, %AST.Var{name: name}, rest}
  defp parse_expr_atom([{:number, _, _, val} | rest]), do: {:ok, %AST.Universe{level: val}, rest}

  defp parse_expr_atom([{:hole, _, _} | rest]), do: {:ok, %AST.Hole{}, rest}

  defp parse_expr_atom([{:backslash, _, _} | rest]) do
    case parse_params(rest, []) do
      {:ok, params, [divider | rest2]} when elem(divider, 0) in [:arrow, :comma] ->
        case parse_expr(rest2) do
          {:ok, body, rest3} ->
            # Fold params into Lam nodes
            expr =
              Enum.reduce(Enum.reverse(params), body, fn
                {name, ty}, acc -> %AST.Lam{name: name, domain: ty, body: acc}
                %AST.Var{name: name}, acc -> %AST.Lam{name: name, domain: %AST.Hole{}, body: acc}
                _, acc -> acc
              end)

            {:ok, expr, rest3}

          err ->
            err
        end

      _ ->
        {:error, :invalid_lambda}
    end
  end

  defp parse_expr_atom([{:left_paren, _, _} | rest]) do
    case parse_expr_list(rest, []) do
      {:ok, exprs, [{:right_paren, _, _} | rest2]} ->
        case exprs do
          [e] -> {:ok, e, rest2}
          _ -> {:ok, %AST.Pair{first: hd(exprs), second: tl(exprs)}, rest2} # simplified pair
        end
      err -> err
    end
  end

  defp parse_expr_atom([{:left_square, _, _} | rest]) do
     case parse_system(rest, []) do
       {:ok, sys, [{:right_square, _, _} | rest2]} -> {:ok, %AST.System{map: sys}, rest2}
       err -> err
     end
  end

  defp parse_expr_atom([{:left_angle, _, _} | rest]) do # < i > e
    case parse_binders(rest, []) do
      {:ok, binders, [{:right_angle, _, _} | rest2]} ->
        case parse_expr(rest2) do
          {:ok, e, rest3} -> {:ok, %AST.PLam{expr: Enum.reduce(binders, e, fn b, acc -> %AST.Lam{name: b.name, domain: %AST.Interval{}, body: acc} end)}, rest3}
          err -> err
        end
      _ -> {:error, :invalid_plam}
    end
  end

  defp parse_expr_atom([{:pathp, _, _} | rest]) do
     case parse_expr_atom(rest) do
       {:ok, p, rest2} -> {:ok, %AST.PathP{path: p}, rest2}
       err -> err
     end
  end

  defp parse_expr_atom([{:transp, _, _} | rest]) do
    case parse_expr_atom(rest) do
      {:ok, p, rest2} ->
        case parse_expr_atom(rest2) do
          {:ok, phi, rest3} -> {:ok, %AST.Transp{path: p, phi: phi}, rest3}
          err -> err
        end
      err -> err
    end
  end

  defp parse_expr_atom([{:hcomp, _, _} | rest]) do
    case parse_expr_atom(rest) do
      {:ok, t, rest2} ->
        case parse_expr_atom(rest2) do
          {:ok, phi, rest3} ->
            case parse_expr_atom(rest3) do
              {:ok, u, rest4} ->
                case parse_expr_atom(rest4) do
                  {:ok, u0, rest5} -> {:ok, %AST.HComp{type: t, phi: phi, u: u, u0: u0}, rest5}
                  err -> err
                end
              err -> err
            end
          err -> err
        end
      err -> err
    end
  end

  defp parse_expr_atom([{:partial, _, _} | rest]) do
    case parse_expr_atom(rest) do
      {:ok, e, rest2} -> {:ok, %AST.Partial{expr: e}, rest2}
      err -> err
    end
  end

  defp parse_expr_atom([{:partialp, _, _} | rest]) do
    case parse_expr_atom(rest) do
      {:ok, t, rest2} ->
        case parse_expr_atom(rest2) do
          {:ok, phi, rest3} -> {:ok, %AST.PartialP{type: t, phi: phi}, rest3}
          err -> err
        end
      err -> err
    end
  end

  defp parse_expr_atom([{:w_type, _, _} | rest]) do
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

  defp parse_expr_atom([{:sup, _, _} | rest]) do
    case parse_expr_atom(rest) do
      {:ok, a, rest2} ->
        case parse_expr_atom(rest2) do
          {:ok, b, rest3} -> {:ok, %AST.Sup{first: a, second: b}, rest3}
          err -> err
        end
      err -> err
    end
  end

  defp parse_expr_atom([{:ind_w, _, _} | rest]) do
    case parse_expr_atom(rest) do
      {:ok, a, rest2} ->
        case parse_expr_atom(rest2) do
          {:ok, b, rest3} ->
            case parse_expr_atom(rest3) do
              {:ok, c, rest4} -> {:ok, %AST.IndW{type: a, expr1: b, expr2: c}, rest4}
              err -> err
            end
          err -> err
        end
      err -> err
    end
  end

  defp parse_expr_atom([{:id_type, _, _} | rest]) do
    case parse_expr_atom(rest) do
      {:ok, t, rest2} -> {:ok, %AST.Id{type: t}, rest2}
      err -> err
    end
  end

  defp parse_expr_atom([{:ref_term, _, _} | rest]) do
    case parse_expr_atom(rest) do
      {:ok, e, rest2} -> {:ok, %AST.Refl{expr: e}, rest2}
      err -> err
    end
  end

  defp parse_expr_atom([{:idj, _, _} | rest]) do
    case parse_expr_atom(rest) do
      {:ok, e, rest2} -> {:ok, %AST.IdJ{expr: e}, rest2}
      err -> err
    end
  end

  defp parse_expr_atom([{:ind_empty, _, _} | rest]) do
    case parse_expr_atom(rest) do
      {:ok, t, rest2} -> {:ok, %AST.IndEmpty{type: t}, rest2}
      err -> err
    end
  end

  defp parse_expr_atom([{:ind_unit, _, _} | rest]) do
    case parse_expr_atom(rest) do
      {:ok, t, rest2} -> {:ok, %AST.IndUnit{type: t}, rest2}
      err -> err
    end
  end

  defp parse_expr_atom([{:ind_bool, _, _} | rest]) do
    case parse_expr_atom(rest) do
      {:ok, t, rest2} -> {:ok, %AST.IndBool{type: t}, rest2}
      err -> err
    end
  end

  defp parse_expr_atom([{:empty_type, _, _} | rest]), do: {:ok, %AST.Empty{}, rest}
  defp parse_expr_atom([{:unit_type, _, _} | rest]), do: {:ok, %AST.Unit{}, rest}
  defp parse_expr_atom([{:bool_type, _, _} | rest]), do: {:ok, %AST.Bool{}, rest}
  defp parse_expr_atom([{:false_kw, _, _} | rest]), do: {:ok, %AST.FalseConstant{}, rest}
  defp parse_expr_atom([{:true_kw, _, _} | rest]), do: {:ok, %AST.TrueConstant{}, rest}
  defp parse_expr_atom([{:star_kw, _, _} | rest]), do: {:ok, %AST.Star{}, rest}

  defp parse_expr_atom(tokens), do: {:error, :no_expr_atom, Enum.take(tokens, 5)}

  defp parse_expr_list(tokens, acc) do
    case parse_expr(tokens) do
      {:ok, e, [{:comma, _, _} | rest]} -> parse_expr_list(rest, [e | acc])
      {:ok, e, rest} -> {:ok, Enum.reverse([e | acc]), rest}
      _ -> {:ok, Enum.reverse(acc), tokens}
    end
  end

  defp parse_system(tokens, acc) do
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

  defp parse_face(tokens) do
    case tokens do
      [{:left_paren, _, _}, {:ident, _, _, p}, {:operator, _, _, "="}, {:number, _, _, d}, {:right_paren, _, _} | rest] ->
        {:ok, {p, d}, rest}
      _ -> {:error, :invalid_face}
    end
  end

  defp parse_expr_app_tail(f, tokens) do
    case tokens do
      [{:appformula, _, _} | rest] ->
        case parse_expr_atom(rest) do
          {:ok, arg, rest2} -> parse_expr_app_tail(%AST.AppFormula{left: f, right: arg}, rest2)
          err -> err
        end
      [{:dot, _, _}, {:number, _, _, 1} | rest] -> parse_expr_app_tail(%AST.Fst{expr: f}, rest)
      [{:dot, _, _}, {:number, _, _, 2} | rest] -> parse_expr_app_tail(%AST.Snd{expr: f}, rest)
      [{:dot, _, _}, {:ident, _, _, name} | rest] -> parse_expr_app_tail(%AST.Field{expr: f, name: name}, rest)
      _ ->
        case parse_expr_atom(tokens) do
          {:ok, arg, rest} -> parse_expr_app_tail(%AST.App{func: f, arg: arg}, rest)
          _ -> {:ok, f, tokens}
        end
    end
  end

  defp mk_pi_tele([], type), do: type
  defp mk_pi_tele([param | rest], type) do
    case param do
      {name, ty} -> %AST.Pi{name: name, domain: ty, codomain: mk_pi_tele(rest, type)}
      %AST.Var{name: name} -> %AST.Pi{name: name, domain: %AST.Hole{}, codomain: mk_pi_tele(rest, type)}
    end
  end

  defp mk_lam_tele([], expr), do: expr
  defp mk_lam_tele([param | rest], expr) do
    case param do
      {name, ty} -> %AST.Lam{name: name, domain: ty, body: mk_lam_tele(rest, expr)}
      %AST.Var{name: name} -> %AST.Lam{name: name, domain: %AST.Hole{}, body: mk_lam_tele(rest, expr)}
    end
  end
end
