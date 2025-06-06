open Printer
open Error
open Exp

let extPiG : value -> value * clos = function | VPi (t, g) -> (t, g) | u -> raise (ExpectedPi (rbV u))
let extSigG : value -> value * clos = function | VSig (t, g) -> (t, g) | u -> raise (ExpectedSig (rbV u))
let extSet : value -> Z.t = function | VPre n | VKan n -> n | v -> raise (ExpectedVSet (rbV v))
let extKan : value -> Z.t = function | VKan n -> n | v -> raise (ExpectedFibrant (rbV v))
let extPathP = function | VApp (VApp (VPathP v, u0), u1) -> (v, u0, u1) | v -> raise (ExpectedPath (rbV v))
let extVar ctx x = match Env.find_opt x ctx with | Some (_, _, Value (Var (y, _))) -> y | Some (_, _, Exp (EVar y)) -> y | _ -> x

let idv t x y = VApp (VApp (VId t, x), y)
let implv a b = VPi (a, (Irrefutable, fun _ -> b))
let hcompval u = EApp (EApp (u, ezero), ERef eone)
let imax a b = match a, b with
  | VKan u, VKan v -> VKan (max u v)
  | VPre u, VPre v | VPre u, VKan v | VKan u, VPre v -> VPre (max u v)
  | VKan _, _ | VPre _, _ -> raise (ExpectedVSet (rbV b))
  | _, _ -> raise (ExpectedVSet (rbV a))

let rec orFormula : value * value -> value = function
  | VDir One, _  | _, VDir One  -> VDir One
  | VDir Zero, f | f, VDir Zero -> f
  | VOr (f, g), h -> orFormula (f, orFormula (g, h))
  | f, g -> VOr (f, g)

let rec andFormula : value * value -> value = function
  | VDir Zero, _ | _, VDir Zero -> VDir Zero
  | VDir One, f  | f, VDir One  -> f
  | VAnd (f, g), h -> andFormula (f, andFormula (g, h))
  | VOr (f, g), h | h, VOr (f, g) -> orFormula (andFormula (f, h), andFormula (g, h))
  | f, g -> VAnd (f, g)

let rec negFormula : value -> value = function
  | VDir d      -> VDir (negDir d)
  | VNeg n      -> n
  | VAnd (f, g) -> orFormula (negFormula f, negFormula g)
  | VOr (f, g)  -> andFormula (negFormula f, negFormula g)
  | v           -> VNeg v

let rec extAnd : value -> conjunction = function
  | Var (x, _)        -> Conjunction.singleton (x, One)
  | VNeg (Var (x, _)) -> Conjunction.singleton (x, Zero)
  | VAnd (x, y)       -> Conjunction.union (extAnd x) (extAnd y)
  | v                 -> raise (ExpectedConjunction (rbV v))

let rec extOr : value -> disjunction = function | VOr (x, y) -> Disjunction.union (extOr x) (extOr y) | k -> Disjunction.singleton (extAnd k)
let uniq t = let super x y = not (Conjunction.equal x y) && Conjunction.subset y x in Disjunction.filter (fun x -> not (Disjunction.exists (super x) t)) t
let orEq f g = Disjunction.equal (uniq (extOr f)) (uniq (extOr g))
let andEq f g = Conjunction.equal (extAnd f) (extAnd g)
let compatible xs ys = Env.merge (fun _ x y -> match x, y with | Some d1, Some d2 -> Some (d1 = d2) | _, _ -> Some true) xs ys |> Env.for_all (fun _ b -> b)
let leq xs ys = Env.for_all (fun k d1 -> match Env.find_opt k ys with | Some d2 -> d1 = d2 | None    -> false) xs
let lt xs ys = not (Env.equal (=) xs ys) && leq xs ys
let comparable xs ys = leq xs ys || leq ys xs
let meet = Env.union (fun _ x y -> if x = y then Some x else raise IncompatibleFaces)
let nubRev xs = let ys = ref [] in List.iter (fun x -> if not (List.mem x !ys) then  ys := x :: !ys) xs; !ys
let meets xs ys = let zs = ref [] in List.iter (fun x -> List.iter (fun y -> try zs := meet x y :: !zs with IncompatibleFaces -> ()) ys) xs; nubRev !zs
let eps : face = Env.empty
let meetss = List.fold_left meets [eps]
let union xs ys = nubRev (List.rev_append xs ys)
let mkSystem xs = System.of_seq (List.to_seq xs)
let unionSystem xs ys = System.union (fun _ _ _ -> raise (Failure "unionSystem")) xs ys
let sign x = function | Zero -> ENeg (EVar x) | One  -> EVar x
let getFace xs = Env.fold (fun x d y -> EAnd (y, sign x d)) xs (EDir One)
let getFormula ts = System.fold (fun x _ e -> EOr (getFace x, e)) ts (EDir Zero)
let singleton p x = Env.add p x Env.empty
let contrAtom : ident * dir -> value = function | (x, Zero) -> VNeg (Var (x, VI)) | (x, One)  -> Var (x, VI)
let contrAnd (t : conjunction) : value = Conjunction.fold (fun e e' -> andFormula (contrAtom e, e')) t (VDir One)
let contrOr (t : disjunction) : value = Disjunction.fold (fun e e' -> orFormula (contrAnd e, e')) t (VDir Zero)
let getFaceV xs = Env.fold (fun x d y -> andFormula (y, contrAtom (x, d))) xs vone
let getFormulaV ts = System.fold (fun x _ v -> orFormula (getFaceV x, v)) ts vzero

let rec solve k x = match k, x with
  | VDir y, _ -> if x = y then [eps] else []
  | Var (p, _), _ -> [singleton p x]
  | VNeg n, _ -> solve n (negDir x)
  | VOr (f, g), One  | VAnd (f, g), Zero -> union (solve f x) (solve g x)
  | VOr (f, g), Zero | VAnd (f, g), One  -> meets (solve f x) (solve g x)
  | _, _ -> failwith (Printf.sprintf "Cannot solve: %s = %s" (showExp (rbV k)) (showDir x))

let freshDim () = let i = freshName "ι" in (i, EVar i, Var (i, VI))
let ieq u v : bool = !girard || u = v
let vfst : value -> value = function | VPair (_, u, _) -> u | v -> VFst v
let vsnd : value -> value = function | VPair (_, _, u) -> u | v -> VSnd v

let rec eval (e0 : exp) (ctx : ctx) = match e0 with
  | EPre u               -> VPre u
  | EKan u               -> VKan u
  | EVar x               -> getRho ctx x
  | EHole                -> VHole
  | EPi  (a, (p, b))     -> let t = eval a ctx in VPi (t, (p, closByVal ctx p t b))
  | ESig (a, (p, b))     -> let t = eval a ctx in VSig (t, (p, closByVal ctx p t b))
  | ELam (a, (p, b))     -> let t = eval a ctx in VLam (t, (p, closByVal ctx p t b))
  | EApp (f, x)          -> app (eval f ctx, eval x ctx)
  | EPair (r, e1, e2)    -> VPair (r, eval e1 ctx, eval e2 ctx)
  | EFst e               -> vfst (eval e ctx)
  | ESnd e               -> vsnd (eval e ctx)
  | EField (e, p)        -> evalField p (eval e ctx)
  | EId e                -> VId (eval e ctx)
  | ERef e               -> VRef (eval e ctx)
  | EJ e                 -> VJ (eval e ctx)
  | EPathP e             -> VPathP (eval e ctx)
  | EPLam e              -> VPLam (eval e ctx)
  | EAppFormula (e, x)   -> appFormula (eval e ctx) (eval x ctx)
  | EI                   -> VI
  | EDir d               -> VDir d
  | EAnd (e1, e2)        -> evalAnd (eval e1 ctx) (eval e2 ctx)
  | EOr (e1, e2)         -> evalOr (eval e1 ctx) (eval e2 ctx)
  | ENeg e               -> negFormula (eval e ctx)
  | ETransp (p, i)       -> VTransp (eval p ctx, eval i ctx)
  | EHComp (t, r, u, u0) -> hcomp (eval t ctx) (eval r ctx) (eval u ctx) (eval u0 ctx)
  | EPartial e           -> let (i, _, _) = freshDim () in VLam (VI, (i, fun r -> let ts = mkSystem (List.map (fun mu -> (mu, eval e (faceEnv mu ctx))) (solve r One)) in VPartialP (VSystem ts, r)))
  | EPartialP (t, r)     -> VPartialP (eval t ctx, eval r ctx)
  | ESystem xs           -> VSystem (evalSystem ctx xs)
  | ESub (a, i, u)       -> VSub (eval a ctx, eval i ctx, eval u ctx)
  | EInc (t, r)          -> VInc (eval t ctx, eval r ctx)
  | EOuc e               -> evalOuc (eval e ctx)
  | EEmpty               -> VEmpty
  | EIndEmpty e          -> VIndEmpty (eval e ctx)
  | EUnit                -> VUnit
  | EStar                -> VStar
  | EIndUnit e           -> VIndUnit (eval e ctx)
  | EBool                -> VBool
  | EFalse               -> VFalse
  | ETrue                -> VTrue
  | EIndBool e           -> VIndBool (eval e ctx)
  | EW (a, (p, b))       -> let t = eval a ctx in VW (t, (fresh p, closByVal ctx p t b))
  | ESup (a, b)          -> VSup (eval a ctx, eval b ctx)
  | EIndW (a, b, c)      -> VIndW (eval a ctx, eval b ctx, eval c ctx)

and appFormula v x = match v with
  | VPLam f -> app (f, x)
  | _       -> let (_, u0, u1) = extPathP (inferV v) in
    begin match x with
      | VDir Zero -> u0
      | VDir One  -> u1
      | i         -> VAppFormula (v, i)
    end

and evalAnd a b = match andFormula (a, b) with | VAnd (a, b) -> contrAnd (extAnd (VAnd (a, b))) | v -> v
and evalOr a b = match orFormula (a, b) with | VOr (a, b) -> contrOr (uniq (extOr (VOr (a, b)))) | v -> v
and border xs v = mkSystem (List.map (fun alpha -> (alpha, upd alpha v)) xs)
and partialv t r = VPartialP (VSystem (border (solve r One) t) , r)

and transport p phi u0 = let (_, _, v) = freshDim () in match appFormula p v, phi with
  (* transp p 1 u₀ ~> u₀ *)
  | _, VDir One -> u0
  (* transp (<_> U) i A ~> A *)
  | VKan _, _ -> u0
  (* transp (<i> Π (x : A i), B i x) φ u₀ ~> λ (x : A 1), transp (<i> B i (transFill (<j> A -j) φ x i)) φ (u₀ (transFill (<j> A -j) φ x 1)) *)
  | VPi _, _ -> let x = fresh (ident "x") in
    let (i, _, _) = freshDim () in let (j, _, _) = freshDim () in
    let (t, _) = extPiG (appFormula p vone) in
    VLam (t, (x, fun x ->
      let v = transFill (VPLam (VLam (VI, (j, fun j ->
        fst (extPiG (appFormula p (negFormula j))))))) phi x in
      transport (VPLam (VLam (VI, (i, fun i ->
        let (_, (_, b)) = extPiG (appFormula p i) in
          b (v (negFormula i))))))
        phi (app (u0, v vone))))
  (* transp (<i> Σ (x : A i), B i x) φ u₀ ~> (transp (<j> A j) φ u₀.1, transp (<i> B i (transFill (<j> A j) φ u₀.1 i)) φ u₀.2) *)
  | VSig _, _ ->
    let (i, _, _) = freshDim () in let (j, _, _) = freshDim () in
    let a = VPLam (VLam (VI, (j, fun j -> fst (extSigG (appFormula p j))))) in
    let v1 = transFill a phi (vfst u0) in
    let v2 = transport (VPLam (VLam (VI, (i, fun i ->
      let (_, (_, b)) = extSigG (appFormula p i) in
        b (v1 i))))) phi (vsnd u0) in
    VPair (ref None, v1 vone, v2)
  (* transp (<i> PathP (P i) (v i) (w i)) φ u₀ ~> <j> comp (λ i, P i @ j) (φ ∨ j ∨ -j) (λ (i : I), [(φ = 1) → u₀ @ j, (j = 0) → v i, (j = 1) → w i]) (u₀ @ j) *)
  | VApp (VApp (VPathP _, _), _), _ ->
    let i = fresh (ident "ι") in let j = fresh (ident "υ") in
    VPLam (VLam (VI, (j, fun j ->
      let uj = appFormula u0 j in let r = orFormula (phi, orFormula (j, negFormula j)) in
      comp (fun i -> let (q, _, _) = extPathP (appFormula p i) in appFormula q j) r
        (VLam (VI, (i, fun i ->
          let (_, v, w) = extPathP (appFormula p i) in
          VSystem (unionSystem (border (solve phi One) uj)
                    (unionSystem (border (solve j Zero) v)
                                 (border (solve j One) w)))))) uj)))
  | _, _ -> VApp (VTransp (p, phi), u0)

and hcomp t r u u0 = match t, r with
  (* hcomp A 1 u u₀ ~> u 1 1=1 *)
  | _, VDir One -> app (app (u, vone), VRef vone)
  (* hcomp (Π (x : A), B x) φ u u₀ ~> λ (x : A), hcomp (B x) φ (λ (i : I), [φ → u i 1=1 x]) (u₀ x) *)
  | VPi (t, (_, b)), _ -> let (i, _, _) = freshDim () in let x = fresh (ident "x") in
    VLam (t, (x, fun x ->
      hcomp (b x) r (VLam (VI, (i, fun i ->
        VSystem (border (solve r One)
          (app (app (app (u, i), VRef vone), x)))))) (app (u0, x))))
  (* hcomp (Σ (x : A), B x) φ u u₀ ~> (hfill A φ (λ (k : I), [(r = 1) → (u k 1=1).1]) u₀.1 1, comp (λ i, B (hfill A φ (λ (k : I), [(r = 1) → (u k 1=1).1]) u₀.1 i)) φ (λ (k : I), [(r = 1) → (u k 1=1).2]) u₀.2) *)
  | VSig (t, (_, b)), _ ->
    let (k, _, _) = freshDim () in
    let v1 = hfill t r (VLam (VI, (k, fun k ->
      VSystem (border (solve r One)
        (vfst (app (app (u, k), VRef vone))))))) (vfst u0) in
    let v2 = comp (v1 >> b) r (VLam (VI, (k, fun k ->
      VSystem (border (solve r One)
        (vsnd (app (app (u, k), VRef vone))))))) (vsnd u0) in
    VPair (ref None, v1 vone, v2)
  (* hcomp (PathP A v w) φ u u₀ ~> <j> hcomp (A @ j) (λ (i : I), [(r = 1) → u i 1=1, (j = 0) → v, (j = 1) → w]) (u₀ @ j) *)
  | VApp (VApp (VPathP t, v), w), _ ->
    let (j, _, _) = freshDim () in let (i, _, _) = freshDim () in
    VPLam (VLam (VI, (j, fun j ->
      hcomp (appFormula t j) (orFormula (r, orFormula (j, negFormula j)))
        (VLam (VI, (i, fun i ->
          (VSystem (unionSystem (border (solve r One) (appFormula (app (app (u, i), VRef vone)) j))
            (unionSystem (border (solve j Zero) v) (border (solve j One) w)))))))
          (appFormula u0 j))))
  | _, _ -> VHComp (t, r, u, u0)

and inc t r v = app (VInc (t, r), v)

and comp t r u u0 =
  let (i, _, _) = freshDim () in let (j, _, _) = freshDim () in
  hcomp (t vone) r (VLam (VI, (i, fun i ->
    let u1 = transport (VPLam (VLam (VI, (j, fun j -> t (orFormula (i, j)))))) i (app (app (u, i), VRef vone)) in
      VSystem (border (solve r One) u1))))
    (transport (VPLam (VLam (VI, (i, t)))) vzero u0)

and hfill t r u u0 j =
  let (i, _, _) = freshDim () in
  hcomp t (orFormula (negFormula j, r))
    (VLam (VI, (i, fun i ->
      VSystem (unionSystem (border (solve r One)
        (app (app (u, andFormula (i, j)), VRef vone)))
          (border (solve j Zero) u0))))) u0

and transFill p phi u0 j = let (i, _, _) = freshDim () in
  transport (VPLam (VLam (VI, (i, fun i -> appFormula p (andFormula (i, j))))))
    (orFormula (phi, negFormula j)) u0

and closByVal ctx p t e v =
  (* dirty hack to handle free variables introduced by type checker, for example, while checking terms like p : Path P a b *)
  let ctx' = match v with
  | Var (x, t) -> if Env.mem x ctx then ctx else upLocal ctx x t v
  | _          -> ctx in
  eval e (upLocal ctx' p t v)

and app : value * value -> value = function
  | VApp (VApp (VApp (VApp (VJ _, _), _), f), _), VRef _ -> f
  | VTransp (p, i), u0 -> transport p i u0
  | VSystem ts, x -> reduceSystem ts x
  | VLam (_, (_, f)), v -> f v
  | VInc _, VOuc v -> v
  | f, x -> VApp (f, x)

and evalSystem ctx ts =
  let ts' = System.fold (fun alpha talpha ->
      Env.bindings alpha
      |> List.rev_map (fun (i, d) -> solve (getRho ctx i) d)
      |> meetss
      |> List.rev_map (fun beta -> (beta, eval talpha (faceEnv beta ctx)))
      |> List.rev_append) ts [] in
  List.filter (fun (alpha, _) -> not (List.exists (fun (beta, _) -> lt beta alpha) ts')) ts' |> mkSystem

and reduceSystem ts x =
  match System.find_opt eps ts with
  | Some v -> v
  | None   -> VApp (VSystem ts, x)

and evalOuc v = match v, inferV v with
  | _, VSub (_, VDir One, u) -> app (u, VRef vone)
  | VApp (VInc _, v), _ -> v
  | _, _ -> VOuc v

and getRho ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value v) -> v
  | Some (_, _, Exp e)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

and act e i ctx = eval (EAppFormula (e, i)) ctx

and inferV v = match v with
  | VPi (t, (x, f)) | VSig (t, (x, f)) -> imax (inferV t) (inferV (f (Var (x, t))))
  | VLam (t, (x, f)) -> VPi (t, (x, fun x -> inferV (f x)))
  | VPLam (VLam (VI, (_, g))) -> let t = VLam (VI, (freshName "ι", g >> inferV)) in VApp (VApp (VPathP (VPLam t), g vzero), g vone)
  | VW (t, (x, f)) -> inferVTele imax t x f
  | Var (_, t)               -> t
  | VFst e                   -> fst (extSigG (inferV e))
  | VSnd e                   -> let (_, (_, g)) = extSigG (inferV e) in g (vfst e)
  | VApp (VTransp (p, _), _) -> appFormula p vone
  | VApp (f, x)              ->
  begin match inferV f with
    | VPartialP (t, _) -> app (t, x)
    | VPi (_, (_, g)) -> g x
    | v -> raise (ExpectedPi (rbV v))
  end
  | VAppFormula (f, x)       -> let (p, _, _) = extPathP (inferV f) in appFormula p x
  | VRef v                   -> VApp (VApp (VId (inferV v), v), v)
  | VPre n                   -> VPre (Z.succ n)
  | VKan n                   -> VKan (Z.succ n)
  | VI                       -> VPre Z.zero
  | VInc (t, i)              -> inferInc t i
  | VOuc v                   ->
  begin match inferV v with
    | VSub (t, _, _) -> t
    | _ -> raise (ExpectedSubtype (rbV v))
  end
  | VId v -> let n = extSet (inferV v) in implv v (implv v (VPre n))
  | VJ v -> inferJ v (inferV v)
  | VPathP p -> let (_, _, v) = freshDim () in let t = inferV (appFormula p v) in
    let v0 = appFormula p vzero in let v1 = appFormula p vone in implv v0 (implv v1 t)
  | VDir _ | VOr _ | VAnd _ | VNeg _ -> VI
  | VTransp (p, _) -> implv (appFormula p vzero) (appFormula p vone)
  | VHComp (t, _, _, _) -> t
  | VSub (t, _, _) -> VPre (extSet (inferV t))
  | VPartialP (VSystem ts, _) ->
  begin match System.choose_opt ts with
    | Some (_, t) -> VPre (extSet (inferV t))
    | None        -> VPre Z.zero
  end
  | VPartialP (t, _) -> inferV (inferV t)
  | VSystem ts -> VPartialP (VSystem (System.map inferV ts), getFormulaV ts)
  | VEmpty | VUnit | VBool -> VKan Z.zero
  | VStar -> VUnit | VFalse | VTrue -> VBool
  | VIndEmpty t -> implv VEmpty t
  | VIndUnit t -> recUnit t
  | VIndBool t -> recBool t
  | VSup (a, b) -> inferSup a b
  | VIndW (a, b, c) -> inferIndW a b c
  | VPLam _ | VPair _ | VHole -> raise (InferError (rbV v))

and inferVTele g t x f = g (inferV t) (inferV (f (Var (x, t))))

and extByTag p : value -> value option = function
  | VPair (t, fst, snd) ->
  begin match !t with
    | Some q -> if p = q then Some fst else extByTag p snd
    | _      -> extByTag p snd
  end
  | _ -> None

and evalField p v =
  match extByTag p v with
  | Some k -> k | None -> begin match inferV v with
    | VSig (_, (q, _)) -> if matchIdent p q then vfst v else evalField p (vsnd v)
    | t -> raise (ExpectedSig (rbV t))
  end

and upd e = function
  | VLam (t, (x, g))     -> VLam (upd e t, (x, g >> upd e))
  | VPair (r, u, v)      -> VPair (r, upd e u, upd e v)
  | VKan u               -> VKan u
  | VPi (t, (x, g))      -> VPi (upd e t, (x, g >> upd e))
  | VSig (t, (x, g))     -> VSig (upd e t, (x, g >> upd e))
  | VPre u               -> VPre u
  | VPLam f              -> VPLam (upd e f)
  | Var (i, VI)          -> begin match Env.find_opt i e with | Some d -> VDir d | None   -> Var (i, VI) end
  | Var (x, t)           -> Var (x, upd e t)
  | VApp (f, x)          -> app (upd e f, upd e x)
  | VFst k               -> vfst (upd e k)
  | VSnd k               -> vsnd (upd e k)
  | VHole                -> VHole
  | VPathP v             -> VPathP (upd e v)
  | VPartialP (t, r)     -> VPartialP (upd e t, upd e r)
  | VSystem ts           -> VSystem (System.bindings ts |> List.filter_map (fun (e', v) -> if compatible e e' then  Some (Env.filter (fun k _ -> not (Env.mem k e)) e', upd e v) else None) |> mkSystem)
  | VSub (t, i, u)       -> VSub (upd e t, upd e i, upd e u)
  | VTransp (p, i)       -> VTransp (upd e p, upd e i)
  | VHComp (t, r, u, u0) -> hcomp (upd e t) (upd e r) (upd e u) (upd e u0)
  | VAppFormula (f, x)   -> appFormula (upd e f) (upd e x)
  | VId v                -> VId (upd e v)
  | VRef v               -> VRef (upd e v)
  | VJ v                 -> VJ (upd e v)
  | VI                   -> VI
  | VDir d               -> VDir d
  | VAnd (u, v)          -> andFormula (upd e u, upd e v)
  | VOr (u, v)           -> orFormula (upd e u, upd e v)
  | VNeg u               -> negFormula (upd e u)
  | VInc (t, r)          -> VInc (upd e t, upd e r)
  | VOuc v               -> evalOuc (upd e v)
  | VEmpty               -> VEmpty
  | VIndEmpty v          -> VIndEmpty (upd e v)
  | VUnit                -> VUnit
  | VStar                -> VStar
  | VIndUnit v           -> VIndUnit (upd e v)
  | VBool                -> VBool
  | VFalse               -> VFalse
  | VTrue                -> VTrue
  | VIndBool v           -> VIndBool (upd e v)
  | VW (t, (x, g))       -> VW (upd e t, (x, g >> upd e))
  | VSup (a, b)          -> VSup (upd e a, upd e b)
  | VIndW (a, b, c)      -> VIndW (upd e a, upd e b, upd e c)

and updTerm alpha = function
  | Exp e   -> Exp e
  | Value v -> Value (upd alpha v)

and faceEnv alpha ctx =
  Env.map (fun (p, t, v) -> if p = Local then (p, updTerm alpha t, updTerm alpha v) else (p, t, v)) ctx
  |> Env.fold (fun p dir -> Env.add p (Local, Value VI, Value (VDir dir))) alpha

and rbV v : exp = match v with
  | VLam (t, g)          -> rbVTele eLam t g
  | VPair (r, u, v)      -> EPair (r, rbV u, rbV v)
  | VKan u               -> EKan u
  | VPi (t, g)           -> rbVTele ePi t g
  | VSig (t, g)          -> rbVTele eSig t g
  | VPre u               -> EPre u
  | VPLam f              -> EPLam (rbV f)
  | Var (x, _)           -> EVar x
  | VApp (f, x)          -> EApp (rbV f, rbV x)
  | VFst k               -> EFst (rbV k)
  | VSnd k               -> ESnd (rbV k)
  | VHole                -> EHole
  | VPathP v             -> EPathP (rbV v)
  | VPartialP (t, r)     -> EPartialP (rbV t, rbV r)
  | VSystem ts           -> ESystem (System.map rbV ts)
  | VSub (a, i, u)       -> ESub (rbV a, rbV i, rbV u)
  | VTransp (p, i)       -> ETransp (rbV p, rbV i)
  | VHComp (t, r, u, u0) -> EHComp (rbV t, rbV r, rbV u, rbV u0)
  | VAppFormula (f, x)   -> EAppFormula (rbV f, rbV x)
  | VId v                -> EId (rbV v)
  | VRef v               -> ERef (rbV v)
  | VJ v                 -> EJ (rbV v)
  | VI                   -> EI
  | VDir d               -> EDir d
  | VAnd (u, v)          -> EAnd (rbV u, rbV v)
  | VOr (u, v)           -> EOr (rbV u, rbV v)
  | VNeg u               -> ENeg (rbV u)
  | VInc (t, r)          -> EInc (rbV t, rbV r)
  | VOuc v               -> EOuc (rbV v)
  | VEmpty               -> EEmpty
  | VIndEmpty v          -> EIndEmpty (rbV v)
  | VUnit                -> EUnit
  | VStar                -> EStar
  | VIndUnit v           -> EIndUnit (rbV v)
  | VBool                -> EBool
  | VFalse               -> EFalse
  | VTrue                -> ETrue
  | VIndBool v           -> EIndBool (rbV v)
  | VW (t, g)             -> rbVTele eW t g
  | VSup (a, b)          -> ESup (rbV a, rbV b)
  | VIndW (a, b, c)      -> EIndW (rbV a, rbV b, rbV c)

and rbVTele ctor t (p, g) = let x = Var (p, t) in ctor p (rbV t) (rbV (g x))

and prune ctx x = match Env.find_opt x ctx with
  | Some (_, _, Exp e)   -> e
  | Some (_, _, Value v) -> rbV v
  | None                 -> raise (VariableNotFound x)

and conv v1 v2 : bool =
  v1 == v2 || begin match v1, v2 with
    | VKan u, VKan v -> ieq u v
    | VPair (_, a, b), VPair (_, c, d) -> conv a c && conv b d
    | VPair (_, a, b), v | v, VPair (_, a, b) -> conv (vfst v) a && conv (vsnd v) b
    | VPi (a, (p, f)), VPi  (b, (_, g))
    | VSig (a, (p, f)), VSig (b, (_, g))
    | VLam (a, (p, f)), VLam (b, (_, g)) ->  let x = Var (p, a) in conv a b && conv (f x) (g x)
    | VLam (a, (p, f)), b | b, VLam (a, (p, f)) -> let x = Var (p, a) in conv (app (b, x)) (f x)
    | VW (a, (p, f)), VW (b, (_, g)) -> let x = Var (p, a) in conv a b && conv (f x) (g x)
    | VPre u, VPre v -> ieq u v
    | VPLam f, VPLam g -> conv f g
    | VPLam f, v | v, VPLam f -> let (_, _, i) = freshDim () in conv (appFormula v i) (app (f, i))
    | Var (u, _), Var (v, _) -> u = v
    | VApp (f, a), VApp (g, b) -> conv f g && conv a b
    | VFst x, VFst y | VSnd x, VSnd y -> conv x y
    | VPathP a, VPathP b -> conv a b
    | VPartialP (t1, r1), VPartialP (t2, r2) -> conv t1 t2 && conv r1 r2
    | VAppFormula (f, x), VAppFormula (g, y) -> conv f g && conv x y
    | VSystem xs, VSystem ys -> keys xs = keys ys && System.for_all (fun _ b -> b) (intersectionWith conv xs ys)
    | VSystem xs, x | x, VSystem xs -> System.for_all (fun alpha y -> conv (app (upd alpha x, VRef vone)) y) xs
    | VTransp (p, i), VTransp (q, j) -> conv p q && conv i j
    | VHComp (t1, r1, u1, v1), VHComp (t2, r2, u2, v2) -> conv t1 t2 && conv r1 r2 && conv u1 u2 && conv v1 v2
    | VSub (a, i, u), VSub (b, j, v) -> conv a b && conv i j && conv u v
    | VOr (x, y), VDir Zero | VAnd (x, y), VDir One  -> conv x v2 && conv y v2
    | VOr (x, y), VDir One  | VAnd (x, y), VDir Zero -> conv x v2 || conv y v2
    | VOr _,  _ | _, VOr _  -> orEq v1 v2
    | VAnd _, _ | _, VAnd _ -> andEq v1 v2
    | VNeg x, VNeg y -> conv x y
    | VI, VI -> true
    | VDir u, VDir v -> u = v
    | VId u, VId v | VJ u, VJ v -> conv u v
    | VInc (t1, r1), VInc (t2, r2) -> conv t1 t2 && conv r1 r2
    | VOuc u, VOuc v -> conv u v
    | VEmpty, VEmpty -> true
    | VIndEmpty u, VIndEmpty v -> conv u v
    | VUnit, VUnit -> true
    | VStar, VStar -> true
    | VIndUnit u, VIndUnit v -> conv u v
    | VBool, VBool -> true
    | VFalse, VFalse -> true
    | VTrue, VTrue -> true
    | VIndBool u, VIndBool v -> conv u v
    | VSup (a1, b1), VSup (a2, b2) -> conv a1 a2 && conv b1 b2
    | VIndW (a1, b1, c1), VIndW (a2, b2, c2) -> conv a1 a2 && conv b1 b2 && conv c1 c2
    | _, _ -> false
  end || convWithSystem (v1, v2) || convId v1 v2

and convWithSystem = function
  | v, VApp (VSystem ts, _) | VApp (VSystem ts, _), v ->
    System.for_all (fun mu -> conv (upd mu v)) ts
  | _, _ -> false

and convId v1 v2 =
  (* Id A a b is proof-irrelevant *)
  try match inferV v1, inferV v2 with
    | VApp (VApp (VId t1, a1), b1), VApp (VApp (VId t2, a2), b2) ->
      conv t1 t2 && conv a1 a2 && conv b1 b2
    | _, _ -> false
  with ExpectedNeutral _ -> false

and eqNf v1 v2 : unit = if conv v1 v2 then () else raise (Ineq (rbV v1, rbV v2))

and lookup (x : ident) (ctx : ctx) = match Env.find_opt x ctx with
  | Some (_, Value v, _) -> v
  | Some (_, Exp e, _)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

and check ctx (e0 : exp) (t0 : value) =
  try match e0, t0 with
  | ELam (a, (p, b)), VPi (t, (_, g)) ->
    ignore (extSet (infer ctx a)); eqNf (eval a ctx) t;
    let x = Var (p, t) in let ctx' = upLocal ctx p t x in check ctx' b (g x)
  | EPair (r, e1, e2), VSig (t, (p, g)) ->
    ignore (extSet (inferV t)); check ctx e1 t;
    check ctx e2 (g (eval e1 ctx));
    begin match p with
      | Ident (v, _) -> r := Some v
      | Irrefutable -> ()
    end
  | EHole, v -> traceHole v ctx
  | EPLam (ELam (EI, (i, e))), VApp (VApp (VPathP p, u0), u1) ->
    let v = Var (i, VI) in let ctx' = upLocal ctx i VI v in
    let v0 = eval e (upLocal ctx i VI vzero) in
    let v1 = eval e (upLocal ctx i VI vone) in
    check ctx' e (appFormula p v); eqNf v0 u0; eqNf v1 u1
  | e, VPre u -> begin
    match infer ctx e with
    | VKan v | VPre v -> if ieq u v then () else raise (Ineq (rbV (VPre u), rbV (VPre v)))
    | t -> raise (Ineq (rbV (VPre u), rbV t))
  end
  | ESystem ts, VPartialP (u, i) ->
    eqNf (eval (getFormula ts) ctx) i;
    System.iter (fun alpha e ->
      check (faceEnv alpha ctx) e
        (app (upd alpha u, VRef vone))) ts;
    checkOverlapping ctx ts
  | e, t -> eqNf (infer ctx e) t
  with ex -> Printf.printf "When trying to typecheck\n  %s\nAgainst type\n  %s\n" (showExp e0) (showExp (rbV t0)); raise ex

and checkOverlapping ctx ts =
  System.iter (fun alpha e1 ->
    System.iter (fun beta e2 ->
      if comparable alpha beta then
        let ctx' = faceEnv (meet alpha beta) ctx in
        eqNf (eval e1 ctx') (eval e2 ctx')
      else ()) ts) ts

and infer ctx e : value = match e with
  | EVar x -> lookup x ctx
  | EKan u -> VKan (Z.succ u)
  | EPi (a, (p, b)) -> inferTele ctx imax p a b
  | ESig (a, (p, b)) | EW (a, (p, b)) -> inferTele ctx imax p a b
  | ELam (a, (p, b)) -> inferLam ctx p a b
  | EApp (f, x) -> begin match infer ctx f with
    | VPartialP (t, i) -> check ctx x (isOne i); app (t, eval x ctx)
    | VPi (t, (_, g)) -> check ctx x t; g (eval x ctx)
    | v -> raise (ExpectedPi (rbV v))
  end
  | EFst e -> fst (extSigG (infer ctx e))
  | ESnd e -> let (_, (_, g)) = extSigG (infer ctx e) in g (vfst (eval e ctx))
  | EField (e, p) -> inferField ctx p e
  | EPre u -> VPre (Z.succ u)
  | EPathP p -> inferPath ctx p
  | EPartial e -> let n = extSet (infer ctx e) in implv VI (VPre n)
  | EPartialP (u, r0) -> check ctx r0 VI; let t = infer ctx u in
  begin match t with
    | VPartialP (ts, r) -> eqNf r (eval r0 ctx); inferV (inferV ts)
    | _ -> failwith "Expected partial function into universe"
  end
  | EAppFormula (f, x) -> check ctx x VI; let (p, _, _) = extPathP (infer ctx (rbV (eval f ctx))) in appFormula p (eval x ctx)
  | ETransp (p, i) -> inferTransport ctx p i
  | EHComp (e, i, u, u0) -> let t = eval e ctx in let r = eval i ctx in ignore (extKan (infer ctx e)); check ctx i VI; check ctx u (implv VI (partialv t r)); check ctx u0 t;
    List.iter (fun phi -> let ctx' = faceEnv phi ctx in eqNf (eval (hcompval u) ctx') (eval u0 ctx')) (solve r One); t
  | ESub (a, i, u) -> let n = extSet (infer ctx a) in check ctx i VI; check ctx u (partialv (eval a ctx) (eval i ctx)); VPre n
  | EI -> VPre Z.zero | EDir _ -> VI
  | ENeg e -> check ctx e VI; VI
  | EOr (e1, e2) | EAnd (e1, e2) -> check ctx e1 VI; check ctx e2 VI; VI
  | EId e -> let v = eval e ctx in let n = extSet (infer ctx e) in implv v (implv v (VPre n))
  | ERef e -> let v = eval e ctx in let t = infer ctx e in VApp (VApp (VId t, v), v)
  | EJ e -> inferJ (eval e ctx) (infer ctx e)
  | EInc (e, r) -> ignore (extKan (infer ctx e)); check ctx r VI; inferInc (eval e ctx) (eval r ctx)
  | EOuc e -> begin match infer ctx e with | VSub (t, _, _) -> t | _ -> raise (ExpectedSubtype e) end
  | ESystem ts -> checkOverlapping ctx ts; VPartialP (VSystem (System.map (infer ctx) ts), eval (getFormula ts) ctx)
  | EEmpty | EUnit | EBool -> VKan Z.zero
  | EStar -> VUnit | EFalse | ETrue -> VBool
  | EIndEmpty e -> ignore (extSet (infer ctx e)); implv VEmpty (eval e ctx)
  | EIndUnit e -> inferInd false ctx VUnit e recUnit
  | EIndBool e -> inferInd false ctx VBool e recBool
  | ESup (a, b) -> let t = eval a ctx in ignore (extSet (infer ctx a)); let (t', (p, g)) = extPiG (infer ctx b) in eqNf t t'; ignore (extSet (g (Var (p, t)))); inferSup t (eval b ctx)
  | EIndW (a, b, c) -> let t = eval a ctx in ignore (extSet (infer ctx a));
    let (t', (p, g)) = extPiG (infer ctx b) in eqNf t t'; ignore (extSet (g (Var (p, t))));
    let (w', (q, h)) = extPiG (infer ctx c) in eqNf (wtype t (eval b ctx)) w';
    ignore (extSet (h (Var (q, w'))));
    inferIndW t (eval b ctx) (eval c ctx)
  | e -> raise (InferError e)

and inferInd fibrant ctx t e f =
  let (t', (p, g)) = extPiG (infer ctx e) in eqNf t t'; let k = g (Var (p, t)) in
  ignore (if fibrant then extKan k else extSet k); f (eval e ctx)

and inferField ctx p e = match infer ctx e with
  | VSig (t, (q, _)) -> if matchIdent p q then t else inferField ctx p (ESnd e)
  | t                -> raise (ExpectedSig (rbV t))

and inferTele ctx g p a b =
  ignore (extSet (infer ctx a));
  let t = eval a ctx in let x = Var (p, t) in
  let ctx' = upLocal ctx p t x in
  let v = infer ctx' b in g (infer ctx a) v

and inferLam ctx p a e =
  ignore (extSet (infer ctx a)); let t = eval a ctx in
  ignore (infer (upLocal ctx p t (Var (p, t))) e);
  VPi (t, (p, fun x -> inferV (eval e (upLocal ctx p t x))))

and inferPath (ctx : ctx) (p : exp) =
  let (i, x, v) = freshDim () in let ctx' = upLocal ctx i VI v in
  let t = infer ctx' (rbV (act p x ctx')) in ignore (extSet t);
  let v0 = act p ezero ctx in let v1 = act p eone ctx in implv v0 (implv v1 t)

and inferInc t r = let a = freshName "a" in
  VPi (t, (a, fun v -> VSub (t, r, VSystem (border (solve r One) v))))

and inferTransport (ctx : ctx) (p : exp) (i : exp) =
  check ctx i VI;
  let u0 = act p ezero ctx in
  let u1 = act p eone  ctx in
  let (j, x, v) = freshDim () in let ctx' = upLocal ctx j VI v in
  ignore (extKan (infer ctx' (rbV (act p x ctx'))));
  List.iter (fun phi -> let rho = faceEnv phi ctx' in eqNf (act p ezero rho) (act p x rho)) (solve (eval i ctx) One);
  implv u0 u1

and inferJ v t =
  let x = freshName "x" in let y = freshName "y" in let pi = freshName "P" in let p = freshName "p" in
  let k = extSet t in let t = VPi (v, (x, fun x -> VPi (v, (y, fun y -> implv (idv v x y) (VPre k))))) in
  VPi (t, (pi, fun pi ->
    VPi (v, (x, fun x ->
      implv (app (app (app (pi, x), x), VRef x))
            (VPi (v, (y, fun y ->
              VPi (idv v x y, (p, fun p ->
                app (app (app (pi, x), y), p))))))))))

and recUnit t = let x = freshName "x" in implv (app (t, VStar)) (VPi (VUnit, (x, fun x -> app (t, x))))
and recBool t = let x = freshName "x" in implv (app (t, VFalse)) (implv (app (t, VTrue)) (VPi (VBool, (x, fun x -> app (t, x)))))
and wtype a b = VW (a, (freshName "x", fun x -> app (b, x)))
and inferSup a b = let t = wtype a b in let x = freshName "x" in VPi (a, (x, fun x -> implv (implv (app (b, x)) t) t))
and inferIndW a b c = let t = wtype a b in
  implv (VPi (a, (freshName "x", fun x ->
    VPi (implv (app (b, x)) t, (freshName "f", fun f ->
      implv (VPi (app (b, x), (freshName "b", fun b -> app (c, (app (f, b))))))
        (app (c, VApp (VApp (VSup (a, b), x), f))))))))
    (VPi (t, (freshName "w", fun w -> app (c, w))))

let rec salt (ns : ident Env.t) : exp -> exp = function
  | EKan n               -> EKan n
  | EPre n               -> EPre n
  | EVar x               -> EVar (freshVar ns x)
  | EHole                -> EHole
  | EPi (a, (p, b))      -> saltTele ePi ns p a b
  | ELam (a, (p, b))     -> saltTele eLam ns p a b
  | EApp (f, x)          -> EApp (salt ns f, salt ns x)
  | ESig (a, (p, b))     -> saltTele eSig ns p a b
  | EPair (r, a, b)      -> EPair (r, salt ns a, salt ns b)
  | EFst e               -> EFst (salt ns e)
  | ESnd e               -> ESnd (salt ns e)
  | EField (e, p)        -> EField (salt ns e, p)
  | EId e                -> EId (salt ns e)
  | ERef e               -> ERef (salt ns e)
  | EJ e                 -> EJ (salt ns e)
  | EPathP e             -> EPathP (salt ns e)
  | ETransp (p, i)       -> ETransp (salt ns p, salt ns i)
  | EHComp (t, r, u, u0) -> EHComp (salt ns t, salt ns r, salt ns u, salt ns u0)
  | EPLam e              -> EPLam (salt ns e)
  | EAppFormula (p, i)   -> EAppFormula (salt ns p, salt ns i)
  | EPartial e           -> EPartial (salt ns e)
  | EPartialP (t, r)     -> EPartialP (salt ns t, salt ns r)
  | ESub (a, i, u)       -> ESub (salt ns a, salt ns i, salt ns u)
  | ESystem xs           -> ESystem (System.fold (fun k v -> System.add (freshFace ns k) (salt ns v)) xs System.empty)
  | EInc (t, r)          -> EInc (salt ns t, salt ns r)
  | EOuc e               -> EOuc (salt ns e)
  | EDir d               -> EDir d
  | EI                   -> EI
  | EAnd (a, b)          -> EAnd (salt ns a, salt ns b)
  | EOr (a, b)           -> EOr (salt ns a, salt ns b)
  | ENeg e               -> ENeg (salt ns e)
  | EEmpty               -> EEmpty
  | EIndEmpty e          -> EIndEmpty (salt ns e)
  | EUnit                -> EUnit
  | EStar                -> EStar
  | EIndUnit e           -> EIndUnit (salt ns e)
  | EBool                -> EBool
  | EFalse               -> EFalse
  | ETrue                -> ETrue
  | EIndBool e           -> EIndBool (salt ns e)
  | EW (a, (p, b))       -> saltTele eW ns p a b
  | ESup (a, b)          -> ESup (salt ns a, salt ns b)
  | EIndW (a, b, c)      -> EIndW (salt ns a, salt ns b, salt ns c)

and freshFace ns phi = Env.fold (fun k v -> Env.add (freshVar ns k) v) phi Env.empty
and saltTele ctor ns p a b = let x = fresh p in ctor x (salt ns a) (salt (Env.add p x ns) b)

let freshTele ns : tele -> tele = fun (p, e) -> let q = fresh p in let e' = salt !ns e in ns := Env.add p q !ns; (q, e')
let freshExp = salt Env.empty
let freshDecl : decl -> decl = function | Def (p, exp1, exp2) -> Def (p, (freshExp exp1), freshExp exp2) | Axiom (p, exp) -> Axiom (p, freshExp exp)
let ext x = x ^ ".per"
let empty : state = (Env.empty, Files.empty)
let getTerm e ctx = if !preeval then Value (eval e ctx) else Exp e

let checkDecl ctx d : ctx =
  let x = getDeclName d in if Env.mem (ident x) ctx then raise (AlreadyDeclared x);
  match d with
  | Def (p, a, e) -> ignore (extSet (infer ctx a)); let t = eval a ctx in let v = ident p in check (upGlobal ctx v t (Var (v, t))) e t; Env.add (ident p) (Global, Value t, getTerm e ctx) ctx
  | Axiom (p, a)  -> ignore (extSet (infer ctx a)); let x = ident p in let t = eval a ctx in Env.add x (Global, Value t, Value (Var (x, t))) ctx

let getBoolVal opt = function
  | "tt" | "true"  -> true
  | "ff" | "false" -> false
  | value -> raise (UnknownOptionValue (opt, value))
