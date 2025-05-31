open Prettyprinter
open Ident
open Expr
open Rbv

let traceHole v gma = ()
let trace x = print_string x; flush_all ()

let traceCheck (e : exp) (t : value) : unit = if !Prefs.trace then
  trace (Printf.sprintf "CHECK: %s : %s\n" (showExp e) (showExp (rbV t)))

let traceInfer (e : exp) : unit = if !Prefs.trace then
  trace (Printf.sprintf "INFER: %s\n" (showExp e))

let traceInferV (v : value) : unit = if !Prefs.trace then
  trace (Printf.sprintf "VALUE: %s\n" (showExp (rbV v)))

let traceEval (e : exp) : unit = if !Prefs.trace then
  trace (Printf.sprintf "EVAL: %s\n" (showExp e))

let traceWeak (e : exp) : unit = if !Prefs.trace then
  trace (Printf.sprintf "WEAK: %s\n" (showExp e))

let traceRbV (v : value) : unit = if !Prefs.trace then
  trace (Printf.sprintf "RBV: %s\n" (showExp (rbV v)))

let traceClos (e : exp) (p : ident) (v : value) : unit = if !Prefs.trace then
  trace (Printf.sprintf "CLOS: (%s)(%s := %s)\n" (showExp e) (showIdent p) (showExp (rbV v)))

let traceConv (v1 : value) (v2 : value) : unit = if !Prefs.trace then
  trace (Printf.sprintf "CONV: %s = %s\n" (showExp (rbV v1)) (showExp (rbV v2)))

let traceEqNF (v1 : value) (v2 : value) : unit = if !Prefs.trace then
  trace (Printf.sprintf "EQNF: %s = %s\n" (showExp (rbV v1)) (showExp (rbV v2)))
