type ident =
  | Irrefutable
  | Ident of string * int64

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
let negDir : dir -> dir = function
  | Zero -> One | One -> Zero

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
let eps : face = Env.empty

module Face =
struct
  type t = face
  let compare = Env.compare Dir.compare
end

module System = Map.Make(Face)

let keys ts = List.of_seq (Seq.map fst (System.to_seq ts))
let intersectionWith f =
  System.merge (fun _ x y ->
    match x, y with
    | Some a, Some b -> Some (f a b)
    | _,      _      -> None)

type tag = (string option) ref

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
