
type ident = Irrefutable | Ident of string * int64

module Ident =
struct
  type t = ident
  let compare x y =
    match (x, y) with
    | Irrefutable, Irrefutable -> 0
    | Irrefutable, Ident _ -> -1
    | Ident _, Irrefutable -> 1
    | Ident (p, a), Ident (q, b) ->
      if p = q then compare a b
      else compare p q
end

module Env = Map.Make(Ident)

type dir = Zero | One

module Dir =
struct
  type t = dir
  let compare a b =
    match a, b with
    | One, Zero -> 1
    | Zero, One -> -1
    | _, _      -> 0
end

type face = dir Env.t

module Face =
struct
  type t = face
  let compare = Env.compare Dir.compare
end

type tag = (string option) ref

module System = Map.Make(Face)

let eps : face = Env.empty
let negDir : dir -> dir = function | Zero -> One | One -> Zero
let keys ts = List.of_seq (Seq.map fst (System.to_seq ts))
let intersectionWith f =
  System.merge (fun _ x y ->
    match x, y with
    | Some a, Some b -> Some (f a b)
    | _,      _      -> None)

(* MLTT-80 (cubical) *)

type exp =
  | EPre of Z.t | EKan of Z.t                                                          (* cosmos *)
  | EVar of ident | EHole                                                           (* variables *)
  | EPi of exp * (ident * exp) | ELam of exp * (ident * exp) | EApp of exp * exp           (* pi *)
  | ESig of exp * (ident * exp) | EPair of tag * exp * exp                              (* sigma *)
  | EFst of exp | ESnd of exp | EField of exp * string                                  (* sigma *)
  | EId of exp | ERef of exp | EJ of exp                                      (* strict equality *)
  | EPathP of exp | EPLam of exp | EAppFormula of exp * exp                     (* path equality *)
  | EI | EDir of dir | EAnd of exp * exp | EOr of exp * exp | ENeg of exp       (* CCHM interval *)
  | ETransp of exp * exp | EHComp of exp * exp * exp * exp                     (* Kan operations *)
  | EPartial of exp | EPartialP of exp * exp | ESystem of exp System.t      (* partial functions *)
  | ESub of exp * exp * exp | EInc of exp * exp | EOuc of exp                (* cubical subtypes *)
  | EEmpty | EIndEmpty of exp                                                               (* 𝟎 *)
  | EUnit | EStar | EIndUnit of exp                                                         (* 𝟏 *)
  | EBool | EFalse | ETrue | EIndBool of exp                                                (* 𝟐 *)
  | EW of exp * (ident * exp) | ESup of exp * exp | EIndW of exp * exp * exp                (* W *)

type tele = ident * exp

type scope = Local | Global

(* Intermediate type checker values *)

type value =
  | VKan of Z.t | VPre of Z.t
  | Var of ident * value | VHole
  | VPi of value * clos | VLam of value * clos | VApp of value * value
  | VSig of value * clos | VPair of tag * value * value | VFst of value | VSnd of value
  | VId of value | VRef of value | VJ of value
  | VPathP of value | VPLam of value | VAppFormula of value * value
  | VI | VDir of dir | VAnd of value * value | VOr of value * value | VNeg of value
  | VTransp of value * value | VHComp of value * value * value * value
  | VPartialP of value * value | VSystem of value System.t
  | VSub of value * value * value | VInc of value * value | VOuc of value
  | VEmpty | VIndEmpty of value
  | VUnit | VStar | VIndUnit of value
  | VBool | VFalse | VTrue | VIndBool of value
  | W of value * clos | VSup of value * value | VIndW of value * value * value

and clos = ident * (value -> value)

and term = Exp of exp | Value of value

and record = scope * term * term

and ctx = record Env.t

type command =
  | Nope
  | Eval    of exp
  | Action  of string
  | Command of string * exp

type decl =
  | Def of string * exp option * exp
  | Axiom of string * exp

type line =
  | Import of string list
  | Option of string * string
  | Decl of decl

type content = line list

type file = string * content

(* Implementation *)

let eLam p a b = ELam (a, (p, b))
let ePi  p a b = EPi  (a, (p, b))
let eSig p a b = ESig (a, (p, b))
let eW   p a b = EW   (a, (p, b))

let ezero = EDir Zero
let eone  = EDir One
let vzero = VDir Zero
let vone  = VDir One

let isOne i = VApp (VApp (VId VI, VDir One), i)
let extFace x e = e (List.map (fun (p, v) -> Var (p, isOne v)) x)

let ident x = Ident (x, 0L)
let decl x = EVar (ident x)

let upVar p x ctx = match p with Irrefutable -> ctx | _ -> Env.add p x ctx
let upLocal ctx p t v = upVar p (Local, Value t, Value v) ctx
let upGlobal ctx p t v = upVar p (Global, Value t, Value v) ctx

let isGlobal : record -> bool = function Global, _, _ -> false | Local, _, _ -> true
let freshVar ns n = match Env.find_opt n ns with Some x -> x | None -> n
let mapFace fn phi = Env.fold (fun p d -> Env.add (fn p) d) phi Env.empty
let freshFace ns = mapFace (freshVar ns)

(* Value to Expression *)

let rec rbV v = match v with
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
  | W (t, g)             -> rbVTele eW t g
  | VSup (a, b)          -> ESup (rbV a, rbV b)
  | VIndW (a, b, c)      -> EIndW (rbV a, rbV b, rbV c)

and rbVTele ctor t (p, g) = let x = Var (p, t) in ctor p (rbV t) (rbV (g x))

let zeroPrim     = ref "0"
let onePrim      = ref "1"
let intervalPrim = ref "I"

let getVar x =
    let xs = [(!intervalPrim, EI);
              (!zeroPrim, EDir Zero);
              (!onePrim, EDir One);
              ("𝟎", EEmpty);     ("empty", EEmpty);
              ("𝟏", EUnit);      ("unit", EUnit);
              ("𝟐", EBool);      ("bool", EBool);
              ("★", EStar);      ("star", EStar);
              ("false", EFalse); ("0₂", EFalse);
              ("true", ETrue);   ("1₂", ETrue)] in
    match List.assoc_opt x xs with Some e -> e | None -> decl x

type formula =
    | Falsehood
    | Equation of ident * dir
    | Truth

exception ExpectedDir of string
let getDir x = if x = !zeroPrim then Zero else if x = !onePrim then One else raise (ExpectedDir x)

let face p e d : formula = match getVar p, e, getDir d with
    | EVar x,  "=", d  -> Equation (x, d)
    | EDir d1, "=", d2 -> if d1 = d2 then Truth else Falsehood
    | _,       _,   _  -> failwith "invalid face"

  let extEquation : formula -> ident * dir = function
    | Equation (x, d) -> (x, d)
    | _               -> raise (Failure "extEquation")

  let parseFace xs =
    if List.mem Falsehood xs then None
    else if List.mem Truth xs then Some eps
    else Some (Env.of_seq (Seq.map extEquation (List.to_seq xs)))

let parsePartial (xs, e) = Option.map (fun ys -> (ys, e)) (parseFace xs)

let impl a b = EPi (a, (Irrefutable, b))
let prod a b = ESig (a, (Irrefutable, b))

let rec telescope ctor e : tele list -> exp = function
    | []           -> e
    | (p, a) :: xs -> ctor p a (telescope ctor e xs)

let rec pLam e : ident list -> exp = function [] -> e | x :: xs -> EPLam (ELam (EI, (x, pLam e xs)))

let getDeclName : decl -> string = function Def (p, _, _) | Axiom (p, _) -> p
