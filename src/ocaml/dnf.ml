open Exp
open Printer

let rec orFormula a b = match a, b with
  | VDir One, _ | _, VDir One -> VDir One
  | VDir Zero, f | f, VDir Zero -> f
  | VOr (f, g), h -> orFormula f (orFormula g h)
  | f, g -> if f = g then f else VOr (f, g)

let rec andFormula a b = match a, b with
  | VDir Zero, _ | _, VDir Zero -> VDir Zero
  | VDir One, f | f, VDir One -> f
  | VAnd (f, g), h -> andFormula f (andFormula g h)
  | f, g -> if f = g then f else VAnd (f, g)

let rec extAnd v = match v with
  | Var (x, _) -> Conjunction.singleton (x, One)
  | VNeg (Var (x, _)) -> Conjunction.singleton (x, Zero)
  | VAnd (x, y) -> Conjunction.union (extAnd x) (extAnd y)
  | VDir One -> Conjunction.empty
  | _ -> raise (Failure "ExpectedConjunction")

let rec extOr v = match v with
  | VOr (x, y) -> Disjunction.union (extOr x) (extOr y)
  | VDir Zero -> Disjunction.empty
  | k -> Disjunction.singleton (extAnd k)

let uniq t =
  let super x y = not (Conjunction.equal x y) && Conjunction.subset y x in
  Disjunction.filter (fun x -> not (Disjunction.exists (super x) t)) t

let unions t1 t2 =
  Disjunction.fold (fun c1 res ->
    Disjunction.fold (fun c2 res' ->
      Disjunction.add (Conjunction.union c1 c2) res'
    ) t2 res
  ) t1 Disjunction.empty
  |> uniq

let negConjunction c =
  Conjunction.fold (fun (x, d) res ->
    Disjunction.add (Conjunction.singleton (x, negDir d)) res
  ) c Disjunction.empty

let negDisjunction d =
  Disjunction.fold (fun c res ->
    unions res (negConjunction c)
  ) d (Disjunction.singleton Conjunction.empty)

let contrAtom : ident * dir -> value = function
  | (x, Zero) -> VNeg (Var (x, VI))
  | (x, One)  -> Var (x, VI)

let contrAnd (t : conjunction) : value =
  Conjunction.fold (fun e e' -> andFormula (contrAtom e) e') t (VDir One)

let contrOr (t : disjunction) : value =
  Disjunction.fold (fun e e' -> orFormula (contrAnd e) e') t (VDir Zero)

let rec negFormula = function
  | VDir d -> VDir (negDir d)
  | VNeg n -> n
  | v -> contrOr (negDisjunction (extOr v))

let evalAnd a b = contrOr (unions (extOr a) (extOr b))
let evalOr a b = contrOr (uniq (Disjunction.union (extOr a) (extOr b)))

let getFaceV xs = Env.fold (fun x d y -> andFormula y (contrAtom (x, d))) xs (VDir One)
let getFormulaV ts = System.fold (fun x _ v -> orFormula (getFaceV x) v) ts (VDir Zero)
