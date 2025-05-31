open Prettyprinter
open Ident
open Expr

exception Restart
exception IncompatibleFaces
exception InferError of exp
exception ExpectedPi of exp
exception ExpectedESet of exp
exception ExpectedSig of exp
exception ExpectedPath of exp
exception ExpectedVSet of exp
exception Ineq of exp * exp
exception ExpectedSubtype of exp
exception Parser of int * string * string
exception ExpectedSystem of exp
exception UnknownOption of string
exception ExpectedNeutral of exp
exception ExpectedFibrant of exp
exception UnknownCommand of string
exception VariableNotFound of ident
exception ExtractionError of string
exception AlreadyDeclared of string
exception UnknownPrimitive of string
exception ExpectedConjunction of exp
exception InvalidModuleName of string * string
exception UnknownOptionValue of string * string

let prettyPrintError : exn -> unit = function
  | Ineq (e1, e2) -> Printf.printf "Type mismatch:\n  %s\nis not equal to\n  %s\n" (showExp e1) (showExp e2)
  | ExpectedConjunction v -> Printf.printf "“%s” expected to be conjunction\n" (showExp v)
  | ExpectedDir s -> Printf.printf "“%s” expected to be “%s” or “%s”" s !zeroPrim !onePrim
  | ExtractionError s -> Printf.printf "Error occured during extraction: %s\n" s
  | ExpectedPath e -> Printf.printf "“%s” expected to be a path.\n" (showExp e)
  | AlreadyDeclared p -> Printf.printf "“%s” is already declared.\n" p
  | InferError e -> Printf.printf "Cannot infer type of\n  %s\n" (showExp e)
  | VariableNotFound p -> Printf.printf "Variable %s was not found\n" (showIdent p)
  | InvalidModuleName (name, filename) -> Printf.printf "Module “%s” does not match name of its file: %s\n" name filename
  | ExpectedESet x -> Printf.printf "  %s\nexpected to be universe\n" (showExp x)
  | ExpectedVSet x -> Printf.printf "  %s\nexpected to be universe\n" (showExp x)
  | ExpectedFibrant x -> Printf.printf "  %s\nexpected to be fibrant universe\n" (showExp x)
  | ExpectedPi x -> Printf.printf "  %s\nexpected to be Pi-type\n" (showExp x)
  | ExpectedSig x -> Printf.printf "  %s\nexpected to be Sigma-type\n" (showExp x)
  | ExpectedNeutral x -> Printf.printf "  %s\nexpected to be neutral\n" (showExp x)
  | ExpectedSystem x -> Printf.printf "  %s\nexpected to be a system\n" (showExp x)
  | ExpectedSubtype x -> Printf.printf "  %s\nexpected to be a cubical subtype\n" (showExp x)
  | UnknownCommand s -> Printf.printf "Unknown command “%s”\n" s
  | UnknownOption opt -> Printf.printf "Unknown option “%s”\n" opt
  | UnknownOptionValue (opt, value) -> Printf.printf "Unknown value “%s” of option “%s”\n" value opt
  | Parser (x, buf, filename) -> Printf.printf "Parsing error at line %d while parsing “%s”: “%s”\n" x filename buf
  | IncompatibleFaces -> Printf.printf "Incompatible faces\n"
  | Sys_error s -> print_endline s
  | Restart -> raise Restart
  | ex -> Printf.printf "Uncaught exception: %s\n" (Printexc.to_string ex)

let handleErrors (f : 'a -> 'b) (x : 'a) (default : 'b) : 'b =
  try f x with ex -> prettyPrintError ex; default