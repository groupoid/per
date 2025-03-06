(* Copyright (c) 2016—2025 Groupoid Infinity *)

let trace: bool = true

type level = int
type name = string

type term =
  | Var of name | Universe of level
  | Pi of name * term * term | Lam of name * term * term | App of term * term
  | Sigma of name * term * term | Pair of term * term | Fst of term | Snd of term
  | Id of term * term * term | Refl of term | J of term * term * term * term * term * term  (* J A a b C d p *)
  | Inductive of inductive | Constr of int * inductive * term list | Elim of inductive * term * term list * term

and inductive = {
  name : string;
  params : (name * term) list;
  level : level;
  constrs : (int * term) list;
  mutual_group : string list
}

type env = (string * inductive) list
type context = (name * term) list

exception TypeError of string

let empty_env : env = []
let empty_ctx : context = []
let add_var ctx x ty = (x, ty) :: ctx

type subst_map = (name * term) list

let rec subst_many m t =
    match t with
    | Var x -> (try List.assoc x m with Not_found -> t)
    | Pi (x, a, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Pi (x, subst_many m a, subst_many m' b)
    | Lam (x, d, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Lam (x, subst_many m d, subst_many m' b)
    | App (f, arg) -> App (subst_many m f, subst_many m arg)
    | Sigma (x, a, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Sigma (x, subst_many m a, subst_many m' b)
    | Pair (a, b) -> Pair (subst_many m a, subst_many m b)
    | Fst t -> Fst (subst_many m t)
    | Snd t -> Snd (subst_many m t)
    | Id (ty, a, b) -> Id (subst_many m ty, subst_many m a, subst_many m b)
    | Refl t -> Refl (subst_many m t)
    | Inductive d -> Inductive d
    | Constr (j, d, args) -> Constr (j, d, List.map (subst_many m) args)
    | Elim (d, p, cases, t') -> Elim (d, subst_many m p, List.map (subst_many m) cases, subst_many m t')
    | J (ty, a, b, c, d, p) -> J (subst_many m ty, subst_many m a, subst_many m b, subst_many m c, subst_many m d, subst_many m p)
    | _ -> t

let subst x s t = subst_many [(x, s)] t

let rec equal env ctx t1 t2 =
    match t1, t2 with
    | App (f, arg), App (f', arg') -> equal env ctx f f' && equal env ctx arg arg'
    | Var x, Var y -> x = y
    | Universe i, Universe j -> i = j
    | Pi (x, a, b), Pi (y, a', b') -> equal env ctx a a' && equal env (add_var ctx x a) b (subst y (Var x) b')
    | Sigma (x, a, b), Sigma (y, a', b') -> equal env ctx a a' && equal env (add_var ctx x a) b (subst y (Var x) b')
    | Pair (a, b), Pair (a', b') -> equal env ctx a a' && equal env ctx b b'
    | Fst t, Fst t' -> equal env ctx t t'
    | Snd t, Snd t' -> equal env ctx t t'
    | Id (ty, a, b), Id (ty', a', b') -> equal env ctx ty ty' && equal env ctx a a' && equal env ctx b b'
    | Refl t, Refl t' -> equal env ctx t t'
    | Inductive d1, Inductive d2 -> d1.name = d2.name && d1.level = d2.level && List.for_all2 (fun (n1, t1) (n2, t2) -> n1 = n2 && equal env ctx t1 t2) d1.params d2.params
    | Constr (j, d1, args1), Constr (k, d2, args2) -> j = k && d1.name = d2.name && List.for_all2 (equal env ctx) args1 args2
    | Elim (d1, p1, cases1, t1), Elim (d2, p2, cases2, t2) -> d1.name = d2.name && equal env ctx p1 p2 && List.for_all2 (equal env ctx) cases1 cases2 && equal env ctx t1 t2
    | J (ty, a, b, c, d, p), J (ty', a', b', c', d', p') -> equal env ctx ty ty' && equal env ctx a a' && equal env ctx b b' && equal env ctx c c' && equal env ctx d d' && equal env ctx p p'
    | _ -> false

and lookup_var ctx x =
    if (trace) then (Printf.printf "Looking up %s in context: [" x;
                     List.iter (fun (n, ty) -> Printf.printf "(%s, " n; print_term ty; print_string "); ") ctx;
                     print_endline "]");
    try Some (List.assoc x ctx) with Not_found -> None

and apply_inductive d args =
    if List.length d.params <> List.length args then raise (TypeError "Parameter mismatch in inductive type");
    let subst_param t = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) t d.params args
    in Inductive { d with constrs = List.map (fun (j, ty) -> (j, subst_param ty)) d.constrs }

and infer env ctx t =
    match t with
    | Var x -> (match lookup_var ctx x with | Some ty -> ty | None -> raise (TypeError ("Unbound variable: " ^ x)))
    | Universe i -> Universe (i + 1)
    | Pi (x, a, b) ->
      let i = check_universe env ctx a in
      let ctx' = add_var ctx x a in
      let j = check_universe env ctx' b in
      let result = Universe (max i j) in
      (if (trace) then (Printf.printf "Inferring Pi %s\n" x;
                       Printf.printf "Domain level: %d\n" i;
                       Printf.printf "Codomain level: %d\n" j;
                       Printf.printf "Pi type: "; print_term result; print_endline "");
      result)
    | Lam (x, domain, body) ->
      check env ctx domain (infer env ctx domain);
      let ctx' = add_var ctx x domain in
      let body_ty = infer env ctx' body in
      let result = Pi (x, domain, body_ty) in
      (if (trace) then (Printf.printf "Inferring Lam %s: domain = " x; print_term domain; print_endline "";
                        Printf.printf "Inferred body type: "; print_term body_ty; print_endline "";
                        Printf.printf "Returning Pi type: "; print_term result; print_endline "");
      result)
    | App (f, arg) ->
      (match infer env ctx f with
        | Pi (x, a, b) -> check env ctx arg a; subst x arg b
        | ty -> Printf.printf "App failed: inferred "; print_term ty; print_endline ""; raise (TypeError "Application requires a Pi type"))
    | Sigma (x, a, b) ->
      let i = check_universe env ctx a in
      let ctx' = add_var ctx x a in
      let j = check_universe env ctx' b in
      Universe (max i j)
    | Pair (a, b) ->
      let a_ty = infer env ctx a in  (* Nat *)
      let b_ty = infer env ctx b in  (* Nat *)
      let expected_b_ty = subst "x" a b_ty in  (* Substitute to ensure dependency, but here b_ty is Nat *)
      check env ctx b b_ty;  (* Just check b has its inferred type *)
      Sigma ("x", a_ty, b_ty)  (* Correctly form Σ(x : Nat).Nat *)
    | Fst p ->
      (match infer env ctx p with
       | Sigma (x, a, b) -> a
       | ty -> raise (TypeError ("Fst expects a Sigma type, got: " ^ (let s = ref "" in print_term_depth 0 ty; !s))))
    | Snd p ->
      (match infer env ctx p with
       | Sigma (x, a, b) -> subst x (Fst p) b
       | ty -> raise (TypeError ("Snd expects a Sigma type, got: " ^ (let s = ref "" in print_term_depth 0 ty; !s))))
    | Id (ty, a, b) ->
      check env ctx a ty;
      check env ctx b ty;
      Universe (check_universe env ctx ty)
    | Refl a ->
      let a_ty = infer env ctx a in
      Id (a_ty, a, a)
    | Inductive d ->
      List.iter (fun (_, ty) -> match infer env ctx ty with | Universe _ -> () | _ -> raise (TypeError "Inductive parameters must be types")) d.params;
      Universe d.level
    | Constr (j, d, args) ->
      let cj = List.assoc j d.constrs in
      let cj_subst = subst_many (List.combine (List.map fst d.params) (List.map snd d.params)) cj in
      check_constructor_args env ctx cj_subst args
    | Elim (d, p, cases, t') -> check_elim env ctx d p cases t'
    | J (ty, a, b, c, d, p) -> check_J env ctx ty a b c d p

and check_universe env ctx t =
    match infer env ctx t with
    | Universe i -> i
    | _ -> raise (TypeError "Expected a universe")

and check_constructor_args env ctx ty args =
    let rec check_args ty args_acc = function
    | [] -> ty
    | arg :: rest ->
        (match ty with
         | Pi (x, a, b) -> check env ctx arg a; check_args (subst x arg b) (arg :: args_acc) rest
         | _ -> raise (TypeError "Too many arguments to constructor"))
    in check_args ty [] args

and check_J env ctx ty a b c d p =
    let a_ty = infer env ctx a in
    if not (equal env ctx a_ty ty) then raise (TypeError "J: First argument must match type A");
    let b_ty = infer env ctx b in
    if not (equal env ctx b_ty ty) then raise (TypeError "J: Second argument must match type A");
    let expected_motive = Pi ("x", ty, Pi ("y", ty, Pi ("p", Id (ty, Var "x", Var "y"), Universe 0))) in
    if (trace) then (Printf.printf "Checking J motive: "; print_term c; print_string " against "; print_term expected_motive; print_endline "");
    check env ctx c expected_motive;
    let ctx_d = add_var ctx "x" ty in
    let c_x_x = App (App (c, Var "x"), Var "x") in
    let refl_x = Refl (Var "x") in
    let expected_d_ty = Pi ("x", ty, App (c_x_x, refl_x)) in
    if (trace) then (Printf.printf "Checking J reflexive case: "; print_term d; print_string " against "; print_term expected_d_ty; print_endline "");
    check env ctx d expected_d_ty;
    check env ctx p (Id (ty, a, b));
    let result = App (App (App (c, a), b), p) in
    if (trace) then (Printf.printf "J result type: "; print_term result; print_endline "");
    result

and check_elim env ctx d p cases t' =
    let t_ty = infer env ctx t' in
    let d_applied = apply_inductive d (List.map snd d.params) in
    if not (equal env ctx t_ty d_applied) then raise (TypeError "Elimination target type mismatch");
    let (x, a, b) = match p with
    | Pi (x, a, b) -> (x, a, b)
    | _ -> raise (TypeError ("Motive must be a Pi type, got: " ^ (let s = ref "" in print_term_depth 0 p; !s))) in
    let p_ty = infer env ctx p in (match p_ty with | Universe _ -> () | _ -> raise (TypeError "Motive must be a type (Universe)"));
    if not (equal env ctx t_ty a) then raise (TypeError "Target type does not match motive domain");
    let result_ty = subst x t' b in
    if (trace) then (Printf.printf "Checking elim for %s\n" d.name;
                     Printf.printf "Target type: "; print_term t_ty; print_endline "";
                     Printf.printf "Motive domain: "; print_term a; print_endline "";
                     Printf.printf "Motive codomain: "; print_term b; print_endline "";
                     Printf.printf "Motive type inferred: "; print_term p_ty; print_endline "";
                     Printf.printf "Result type: "; print_term result_ty; print_endline "");
    if List.length cases <> List.length d.constrs then raise (TypeError "Number of cases doesn't match constructors");
    List.iteri (fun j case ->
      let j_idx = j + 1 in
      let cj = List.assoc j_idx d.constrs in
      let cj_subst = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) cj d.params (List.map snd d.params) in
      let rec compute_case_type ty ctx_acc =
        match ty with
        | Pi (x, a, b) ->
            let var = Var x in let ctx' = add_var ctx_acc x a in let b_ty = compute_case_type b ctx' in
            if equal env ctx a d_applied then Pi (x, a, Pi ("ih", App (p, var), b_ty)) else Pi (x, a, b_ty)
        | Inductive d' when d'.name = d.name -> b
        | _ -> raise (TypeError "Invalid constructor return type")
      in
      let expected_ty = compute_case_type cj_subst ctx in
      if (trace) then (Printf.printf "Checking case %d: " j; print_term case; Printf.printf " against: "; print_term expected_ty; print_endline "");
      check env ctx case expected_ty;
      if (trace) then Printf.printf "Case %d checked\n" j
    ) cases;
    result_ty

and check env ctx t ty =
    if (trace) then (Printf.printf "Checking: "; print_term t; print_string " against "; print_term ty; print_endline "");
    match t, ty with
    | Pi (x, a, b), Pi (y, a', b') ->
        if not (equal env ctx a a') then raise (TypeError "Pi domain mismatch");
        let ctx' = add_var ctx x a in
        check env ctx' b (subst y (Var x) b')
    | Lam (x, domain, body), Pi (y, a, b) ->
        check env ctx domain (infer env ctx domain);
        check env (add_var ctx x domain) body b
    | Constr (j, d, args), Inductive d' when d.name = d'.name ->
        let inferred = infer env ctx t in if not (equal env ctx inferred ty) then raise (TypeError "Constructor type mismatch")
    | Elim (d, p, cases, t'), ty ->
        let inferred = check_elim env ctx d p cases t' in
        if not (equal env ctx inferred ty) then raise (TypeError "Elimination type mismatch")
    | Pair (a, b), Sigma (x, a_ty, b_ty) ->
        check env ctx a a_ty;
        check env ctx b (subst x a b_ty)
    | Fst p, ty ->
        let p_ty = infer env ctx p in
        (match p_ty with
         | Sigma (x, a, _) -> if not (equal env ctx a ty) then raise (TypeError "Fst type mismatch")
         | _ -> raise (TypeError "Fst expects a Sigma type"))
    | Snd p, ty ->
        let p_ty = infer env ctx p in
        (match p_ty with
         | Sigma (x, a, b) -> if not (equal env ctx (subst x (Fst p) b) ty) then raise (TypeError "Snd type mismatch")
         | _ -> raise (TypeError "Snd expects a Sigma type"))
    | Refl a, Id (ty, a', b') ->
      let a_ty = infer env ctx a in
      if not (equal env ctx a_ty ty) then raise (TypeError "Refl argument type mismatch");
      if not (equal env ctx a a') || not (equal env ctx a b') then raise (TypeError "Refl arguments mismatch")
    | _, _ ->
        let inferred = infer env ctx t in
        let ty' = normalize env ctx ty in
        (if (trace) then (Printf.printf "Inferred: "; print_term inferred; print_string ", Expected: "; print_term ty'; print_endline ""));
        match inferred, ty' with
        | Universe i, Universe j when i >= j -> () (* cumulativity *)
        | _ -> if not (equal env ctx inferred ty') then raise (TypeError "Type mismatch")

and reduce env ctx t =
    if (trace) then (Printf.printf "Reducing: "; print_term t; print_endline "");
    match t with
    | App (Lam (x, domain, body), arg) -> subst x arg body
    | App (Pi (x, a, b), arg) -> subst x arg b
    | App (f, arg) -> let f' = reduce env ctx f in if equal env ctx f f' then App (f, reduce env ctx arg) else App (f', arg)
    | Elim (d, p, cases, Constr (j, d', args)) when d.name = d'.name ->
      let case = List.nth cases (j - 1) in let cj = List.assoc j d.constrs in
      let cj_subst = subst_many (List.combine (List.map fst d.params) (List.map snd d.params)) cj in
      apply_case env ctx d p cases case cj_subst args
    | Elim (d, p, cases, t') -> let t'' = reduce env ctx t' in if equal env ctx t' t'' then t else Elim (d, p, cases, t'')
    | Constr (j, d, args) -> Constr (j, d, List.map (reduce env ctx) args)
    | Fst (Pair (a, b)) -> a
    | Snd (Pair (a, b)) -> b
    | J (ty, a, b, c, d, Refl a') when equal env ctx a a' && equal env ctx b a' -> if (trace) then (Printf.printf "Reducing J with refl: "; print_term t; print_string " to "; print_term (App (d, a)); print_endline ""); App (d, a)
    | J (ty, a, b, c, d, p) -> let p' = reduce env ctx p in if equal env ctx p p' then t else J (ty, a, b, c, d, p')
    | Refl a -> let a' = reduce env ctx a in if equal env ctx a a' then t else Refl a'
    | _ -> t

and apply_case env ctx d p cases case ty args =
    if (trace) then (Printf.printf "Applying case: "; print_term case; Printf.printf " to type: "; print_term ty; Printf.printf " with args: [";
                     List.iter (fun arg -> print_term arg; print_string "; ") args;
                     print_endline "]");
    let rec apply ty args_acc remaining_args =
    match ty, remaining_args with
    | Pi (x, a, b), arg :: rest ->
        let b' = subst x arg b in
        let rec_arg =
          if equal env ctx a (Inductive d) then
            match arg with
            | Constr (j, d', sub_args) when d.name = d'.name ->
                let reduced = reduce env ctx (Elim (d, p, cases, arg)) in
                if (trace) then (Printf.printf "Recursive arg for %s: " x; print_term reduced; print_endline "");
                Some reduced
            | _ -> None
          else None
        in
        let new_args_acc = match rec_arg with | Some r -> r :: arg :: args_acc | None -> arg :: args_acc in
        apply b' new_args_acc rest
    | Pi (_, _, b), [] -> apply b args_acc []  (* Handle missing args by skipping to codomain *)
    | _, [] ->
        let rec apply_term t args =
          match t, args with
          | Lam (x, _, body), arg :: rest -> apply_term (subst x arg body) rest
          | t, [] -> t
          | _ -> raise (TypeError "Case application mismatch: too few arguments for lambda")
        in apply_term case (List.rev args_acc)
    | _ -> raise (TypeError "Constructor argument mismatch")
    in apply ty [] args

and normalize env ctx t =
    let t' = reduce env ctx t in
    if (trace) then (Printf.printf "One-step β-reductor: "; print_term t'; print_endline "");
    if equal env ctx t t' then t else normalize env ctx t'

and print_term_depth depth t =
    if depth > 10 then print_string "<deep>"
    else match t with
    | Var x -> print_string x
    | Universe i -> print_string ("Type" ^ string_of_int i)
    | Pi (x, a, b) ->
        print_string ("Π(" ^ x ^ " : ");
        print_term_depth (depth + 1) a;
        print_string ").";
        print_term_depth (depth + 1) b
    | Lam (x, _, body) ->
        print_string ("λ" ^ x ^ ".");
        print_term_depth (depth + 1) body
    | App (f, arg) ->
        print_string "(";
        print_term_depth (depth + 1) f;
        print_string " ";
        print_term_depth (depth + 1) arg;
        print_string ")"
    | Sigma (x, a, b) ->
        print_string ("Σ(" ^ x ^ " : ");
        print_term_depth (depth + 1) a;
        print_string ").";
        print_term_depth (depth + 1) b
    | Pair (a, b) ->
        print_string "(";
        print_term_depth (depth + 1) a;
        print_string ", ";
        print_term_depth (depth + 1) b;
        print_string ")"
    | Fst t ->
        print_string "fst ";
        print_term_depth (depth + 1) t
    | Snd t ->
        print_string "snd ";
        print_term_depth (depth + 1) t
    | Id (ty, a, b) ->
        print_string "{";
        print_term_depth (depth + 1) a;
        print_string " = ";
        print_term_depth (depth + 1) b;
        print_string " : ";
        print_term_depth (depth + 1) ty;
        print_string "}"
    | Refl t ->
        print_string "refl ";
        print_term_depth (depth + 1) t
    | J (ty, a, b, c, d, p) ->
        print_string "J(";
        print_term_depth (depth + 1) ty;
        print_string ", ";
        print_term_depth (depth + 1) a;
        print_string ", ";
        print_term_depth (depth + 1) b;
        print_string ", ";
        print_term_depth (depth + 1) c;
        print_string ", ";
        print_term_depth (depth + 1) d;
        print_string ", ";
        print_term_depth (depth + 1) p;
        print_string ")"
    | Constr (i, d, args) ->
        print_string d.name;
        print_string ".";
        print_string (string_of_int i);
        List.iteri (fun j c ->
          if j > 0 then print_string "; ";
          print_term_depth (depth + 1) c
        ) args
    | Elim (d, p, cases, t') ->
        print_string (d.name ^ ".elim ");
        print_term_depth (depth + 1) p;
        print_string " [";
        List.iteri (fun i c ->
          if i > 0 then print_string "; ";
          print_term_depth (depth + 1) c
        ) cases;
        print_string "] ";
        print_term_depth (depth + 1) t'
    | Inductive d -> print_string d.name

and print_term t = print_term_depth 0 t

(* Example definitions *)

let nat_def = {
  name = "Nat";
  params = [];
  level = 0;
  constrs = [
    (1, Inductive { name = "Nat"; params = []; level = 0; constrs = []; mutual_group = ["Nat"] });
    (2, Pi ("n", Inductive { name = "Nat"; params = []; level = 0; constrs = []; mutual_group = ["Nat"] },
           Inductive { name = "Nat"; params = []; level = 0; constrs = []; mutual_group = ["Nat"] }))
  ];
  mutual_group = ["Nat"]
}

let list_def (a : term) = {
  name = "List";
  params = [("A", a)];
  level = (match a with Universe i -> i | _ -> failwith "List param must be a type");
  constrs = [
    (1, Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = []; mutual_group = ["List"] }); (* nil *)
    (2, Pi ("x", a, Pi ("xs", Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = []; mutual_group = ["List"] },
                        Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = []; mutual_group = ["List"] }))) (* cons *)
  ];
  mutual_group = ["List"]
}

let env = [("Nat", nat_def); ("List", list_def (Universe 0))]
let nat_ind = Inductive nat_def
let list_ind = Inductive (list_def (Universe 0))

let list_length =
  Lam ("l", list_ind,  (* l : List Type0 *)
    Elim ((list_def (Universe 0)),
          Pi ("_", list_ind, nat_ind),
          [Constr (1, nat_def, []);  (* nil -> zero *)
           Lam ("x", Universe 0,  (* x : Type0 *)
             Lam ("xs", list_ind,  (* xs : List Type0 *)
               Lam ("ih", nat_ind,  (* ih : Nat *)
                 Constr (2, nat_def, [Var "ih"]))))], (* succ ih *)
          Var "l"))

let sample_list =
  Constr (2, list_def (Universe 0),  (* cons *)
    [Constr (1, nat_def, []);        (* zero *)
     Constr (2, list_def (Universe 0),  (* cons *)
       [Constr (2, nat_def, [Constr (1, nat_def, [])]);  (* succ zero *)
        Constr (1, list_def (Universe 0), [])])])         (* nil *)

let plus =
  Lam ("m", nat_ind, Lam ("n", nat_ind,
    Elim (nat_def,
          Pi ("_", nat_ind, nat_ind),
          [Var "m"; Lam ("k", nat_ind, Lam ("ih", nat_ind, Constr (2, nat_def, [Var "ih"])))],
          Var "n")))

let plus_ty = Pi ("m", nat_ind, Pi ("n", nat_ind, nat_ind))

let nat_elim =
    Elim (nat_def,
          Pi ("x", nat_ind, Universe 0),
          [Inductive nat_def; Lam ("n", nat_ind, Lam ("ih", Universe 0, Var "ih"))],
          Constr (1, nat_def, []))

let succ = Lam ("n", nat_ind, Constr (2, nat_def, [Var "n"]))

let id_symmetry =  (* Symmetry: a = b → b = a *)
  Lam ("a", nat_ind, Lam ("b", nat_ind, Lam ("p", Id (nat_ind, Var "a", Var "b"),
    J (nat_ind, Var "a", Var "b",
       Pi ("x", nat_ind, Pi ("y", nat_ind, Pi ("p", Id (nat_ind, Var "x", Var "y"), Id (nat_ind, Var "y", Var "x")))),
       Lam ("x", nat_ind, Refl (Var "x")),
       Var "p"))))

let id_transitivity =  
  Lam ("a", nat_ind, Lam ("b", nat_ind, Lam ("c", nat_ind,
    Lam ("p", Id (nat_ind, Var "a", Var "b"), Lam ("q", Id (nat_ind, Var "b", Var "c"),
      J (nat_ind, Var "a", Var "b",
         Pi ("x", nat_ind, Pi ("y", nat_ind, Pi ("p", Id (nat_ind, Var "x", Var "y"), Id (nat_ind, Var "x", Var "c")))),
         Lam ("x", nat_ind, Var "q"),  (* q is still used, but we need to adjust check_J *)
         Var "p"))))))

let empty_ctx : context = []

let test () =
  let ctx = empty_ctx in
  let zero = Constr (1, nat_def, []) in
  let one = Constr (2, nat_def, [zero]) in
  let two = Constr (2, nat_def, [one]) in
  let add_term = App (App (plus, two), two) in
  let add_normal = normalize env empty_ctx add_term in

  let pair_term = Pair (zero, one) in
  let pair_ty = Sigma ("x", nat_ind, nat_ind) in
  let fst_term = Fst pair_term in
  let snd_term = Snd pair_term in
  let id_term = Refl zero in
  let id_ty = Id (nat_ind, zero, zero) in

  let sym_term = App (App (App (id_symmetry, zero), zero), Refl zero) in
  let trans_term = App (App (App (App (App (id_transitivity, zero), one), one), Refl zero), Refl one) in

  Printf.printf "Nat.add: "; print_term add_normal; print_endline "";
  Printf.printf "List.length: "; print_term (normalize env empty_ctx (App (list_length, sample_list))); print_endline "";
  Printf.printf "Nat.Elim: "; print_term nat_elim; print_endline "";

  try
    let succ_ty = infer env ctx succ in
    Printf.printf "typeof(Nat.succ): "; print_term succ_ty; print_endline "";
    let plus_ty = infer env ctx plus in
    Printf.printf "typeof(Nat.plus): "; print_term plus_ty; print_endline "";
    let nat_elim_ty = infer env ctx nat_elim in
    Printf.printf "typeof(Nat.elim): "; print_term nat_elim_ty; print_endline "";
    check env ctx pair_term pair_ty;
    Printf.printf "typeof(Sigma.pair): "; print_term pair_term; print_endline "";
    let fst_ty = infer env ctx fst_term in
    Printf.printf "typeof(Sigma.fst(Sigma.pair)): "; print_term fst_ty; print_endline "";
    let snd_ty = infer env ctx snd_term in
    Printf.printf "typeof(Sigma.snd(Sigma.pair)): "; print_term snd_ty; print_endline "";
    let sym_ty = infer env ctx sym_term in
    Printf.printf "typeof(symmetry zero zero refl): "; print_term sym_ty; print_endline "";
    Printf.printf "symmetry reduces to: "; print_term (normalize env ctx sym_term); print_endline ""; 
    check env ctx id_term id_ty;
    Printf.printf "Refl typechecks\n";

    let trans_ty = infer env ctx trans_term in 
    Printf.printf "typeof(transitivity zero one one refl refl): "; print_term trans_ty; print_endline "";  
    Printf.printf "transitivity reduces to: "; print_term (normalize env ctx trans_term); print_endline ""; 
    Printf.printf "Checking id_term: "; print_term id_term; print_string " against "; print_term id_ty; print_endline ""; 

    with TypeError msg -> print_endline ("Type error: " ^ msg)

let _ = test ()
