open Exp

let showIdent : ident -> string = function
  | Irrefutable -> "_"
  | Ident (p, n) -> if !indices then p ^ "#" ^ Int64.to_string n else p

let showDir : dir -> string = function | Zero -> !zeroPrim | One -> !onePrim

let showFace phi =
  if Env.is_empty phi then "(1 = 1)"
  else Env.bindings phi
       |> List.map (fun (x, d) -> Printf.sprintf "(%s = %s)" (showIdent x) (showDir d))
       |> String.concat " "

let showSystem show xs =
  System.bindings xs
  |> List.map (fun (x, e) -> Printf.sprintf "%s → %s" (showFace x) (show e))
  |> String.concat ", "

let rec ppExp paren e =
  let x = match e with
  | EKan n -> "U" ^ showSubscript n
  | EPre n -> "V" ^ showSubscript n
  | EVar p -> showIdent p
  | EHole -> "?"
  | EPi (a, (p, b)) -> showPiExp a p b
  | ELam (a, (p, b)) -> Printf.sprintf "λ %s, %s" (showTeleExp (p, a)) (showExp b)
  | EApp (f, x) -> Printf.sprintf "%s %s" (showExp f) (ppExp true x)
  | ESig (a, (p, b)) -> Printf.sprintf "Σ %s, %s" (showTeleExp (p, a)) (showExp b)
  | EPair (_, fst, snd) -> Printf.sprintf "(%s, %s)" (showExp fst) (showExp snd)
  | EFst exp -> ppExp true exp ^ ".1"
  | ESnd exp -> ppExp true exp ^ ".2"
  | EField (exp, field) -> ppExp true exp ^ "." ^ field
  | EPLam (ELam (_, (i, e))) -> Printf.sprintf "<%s> %s" (showIdent i) (showExp e)
  | EPLam _ -> failwith "showExp: unreachable code was reached"
  | EAppFormula (f, x) -> Printf.sprintf "%s @ %s" (ppExp true f) (ppExp true x)
  | ESystem x -> Printf.sprintf "[%s]" (showSystem showExp x)
  | ESub (a, i, u) -> Printf.sprintf "%s[%s ↦ %s]" (ppExp true a) (showExp i) (showExp u)
  | EI -> !intervalPrim | EDir d -> showDir d
  | EAnd (a, b) -> Printf.sprintf "%s ∧ %s" (ppExp true a) (ppExp true b)
  | EOr (a, b) -> Printf.sprintf "%s ∨ %s" (ppExp true a) (ppExp true b)
  | ENeg a -> Printf.sprintf "-%s" (ppExp paren a)
  | ETransp (p, i) -> Printf.sprintf "transp %s %s" (ppExp true p) (ppExp true i)
  | EPathP e -> "PathP " ^ ppExp true e
  | EId e -> Printf.sprintf "Id %s" (ppExp true e)
  | ERef e -> Printf.sprintf "ref %s" (ppExp true e)
  | EJ e -> Printf.sprintf "idJ %s" (ppExp true e)
  | EEmpty -> "𝟎" | EUnit -> "𝟏" | EBool -> "𝟐"
  | EStar -> "★" | EFalse -> "0₂" | ETrue -> "1₂"
  | EIndEmpty e -> Printf.sprintf "ind₀ %s" (ppExp true e)
  | EIndUnit e  -> Printf.sprintf "ind₁ %s" (ppExp true e)
  | EIndBool e  -> Printf.sprintf "ind₂ %s" (ppExp true e)
  | ESup (a, b) -> Printf.sprintf "sup %s %s" (ppExp true a) (ppExp true b)
  | EIndW (a, b, c) -> Printf.sprintf "indᵂ %s %s %s" (ppExp true a) (ppExp true b) (ppExp true c)
  | EHComp (t, r, u, u0) -> Printf.sprintf "hcomp %s %s %s %s" (ppExp true t) (ppExp true r) (ppExp true u) (ppExp true u0)
  | EPartial e -> Printf.sprintf "Partial %s" (ppExp true e)
  | EPartialP (t, r) -> Printf.sprintf "PartialP %s %s" (ppExp true t) (ppExp true r)
  | EInc (t, r) -> Printf.sprintf "inc %s %s" (ppExp true t) (ppExp true r)
  | EOuc e -> Printf.sprintf "ouc %s" (ppExp true e)
  | EW (a, (p, b)) -> Printf.sprintf "W %s, %s" (showTeleExp (p, a)) (showExp b)
 in match e with | EVar _ | EFst _ | ESnd _ | EI | EPre _ | ESystem _ | EKan _
                 | EHole | EDir _ | EPair _ | ENeg _ | EW _ -> x | _ -> if paren then "(" ^ x ^ ")" else x

and showExp e = ppExp false e
and showTeleExp a = match a with | (p, x) -> Printf.sprintf "(%s : %s)" (showIdent p) (showExp x)
and showPiExp a p b = match p with
  | Irrefutable -> Printf.sprintf "%s → %s" (ppExp true a) (showExp b)
  | _           -> Printf.sprintf "Π %s, %s" (showTeleExp (p, a)) (showExp b)
