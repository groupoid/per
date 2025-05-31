open Exp
open Prelude

type name =
  | Irrefutable
  | Name of string * int

let showName : name -> string = function
  | Irrefutable -> "_"
  | Name (p, n) -> if !Prefs.indices then p ^ "#" ^ string_of_int n else p

module Name =
struct
  type t = name
  let compare x y =
    match (x, y) with
    | Irrefutable, Irrefutable -> 0
    | Irrefutable, Name _ -> -1
    | Name _, Irrefutable -> 1
    | Name (p, a), Name (q, b) ->
      if p = q then compare a b
      else compare p q
end

module Env = Map.Make(Ident)
type face  = dir Env.t

module Dir =
struct
  type t = dir
  let compare a b =
    match a, b with
    | One, Zero -> 1
    | Zero, One -> -1
    | _, _      -> 0
end

module Files = Set.Make(String)

let gidx : int64 ref = ref 0L
let gen () = gidx := Int64.succ !gidx; !gidx

let fresh : ident -> ident = function
  | Irrefutable  -> let n = gen () in Ident ("x" ^ showSubscript (Z.of_int64 n), n)
  | Ident (p, _) -> Ident (p, gen ())

let freshName x = let n = gen () in Ident (x ^ showSubscript (Z.of_int64 n), n)

let matchIdent p : ident -> bool = function
  | Irrefutable -> false | Ident (q, _) -> p = q

let getDigit x = Char.chr (x + 0x80) |> Printf.sprintf "\xE2\x82%c"

module Atom =
struct
  type t = ident * dir
  let compare (a, x) (b, y) =
    if a = b then Dir.compare x y else Ident.compare a b
end

module Conjunction = Set.Make(Atom)
type conjunction = Conjunction.t

module Disjunction = Set.Make(Conjunction)
type disjunction = Disjunction.t

let zeroPrim     = ref "0"
let onePrim      = ref "1"
let intervalPrim = ref "I"

exception ExpectedDir of string
let getDir x = if x = !zeroPrim then Zero else if x = !onePrim then One else raise (ExpectedDir x)
