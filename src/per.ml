open Printer
open Error
open Check
open Exp

let help =
"Available commands:
  <statement>    infer type and normalize statement
  :q             quit
  :r             restart
  :h             display this message"

let init : state = empty
let st : state ref = ref init

let checkAndEval ctx e : value * value =
  (Check.infer ctx e, Check.eval e ctx)

let main ctx : command -> unit = function
  | Eval e -> let (t, v) = checkAndEval ctx (freshExp e) in
    Printf.printf "TYPE: %s\nEVAL: %s\n" (showExp (rbV t)) (showExp (rbV v))
  | Action "q" -> exit 0
  | Action "r" -> st := init; raise Restart
  | Action "h" -> print_endline help
  | Command (s, _) | Action s -> raise (UnknownCommand s)
  | Nope -> ()

let check filename =
  st := handleErrors (Reader.checkFile !st) filename !st

let banner = "Per theorem prover [MLTT-80] version 0.5.0"

let loop () =
  print_endline ("\n" ^ banner) ;
  let (ctx, _) = !st in
  try while true do
    print_string "> ";
    let line = read_line () in
    handleErrors (fun x ->
      let cmd = Reader.parseErr Parser.repl (Lexing.from_string x) "<stdin>" in
        main ctx cmd) line ()
  done with End_of_file -> ()

type cmdline =
  | Check     of string
  | Lex       of string
  | Parse     of string
  | Prim      of string * string
  | Repl | Help | Trace
  | Indices | Girard | Silent | Irrelevance

let help =
"\n  invocation = per | per list
        list = [] | command list
   primitive = zero | one | interval

     command = check <filename>      | lex <filename>
             | parse <filename>      | girard
             | trace                 | repl
             | help "

let repl = ref false
let cmd : cmdline -> unit = function
  | Check     filename -> check filename
  | Lex       filename -> Reader.lex filename
  | Parse     filename -> Reader.parse filename
  | Prim (prim, value) -> begin match prim with
    | "zero"     -> zeroPrim     := value
    | "one"      -> onePrim      := value
    | "interval" -> intervalPrim := value
    | _ -> raise (UnknownPrimitive prim)
  end
  | Help -> print_endline banner ; print_endline help
  | Repl -> repl := true
  | Silent -> verbose := false
  | Indices -> indices := true
  | Trace -> indices := true; trace := true
  | Girard -> girard := true
  | Irrelevance  -> irrelevance := true

let rec parseArgs : string list -> cmdline list = function
  | [] -> []
  | "prim" :: prim :: value :: rest -> Prim (prim, value) :: parseArgs rest
  | "check"     :: filename :: rest -> Check     filename :: parseArgs rest
  | "lex"       :: filename :: rest -> Lex       filename :: parseArgs rest
  | "parse"     :: filename :: rest -> Parse     filename :: parseArgs rest
  | "help"      :: rest             -> Help    :: parseArgs rest
  | "trace"     :: rest             -> Trace   :: parseArgs rest
  | "indices"   :: rest             -> Indices :: parseArgs rest
  | "irrelevance" :: rest           -> Irrelevance :: parseArgs rest
  | "silent"    :: rest             -> Silent  :: parseArgs rest
  | "girard"    :: rest             -> Girard  :: parseArgs rest
  | "repl"      :: rest             -> Repl    :: parseArgs rest
  | x :: xs -> Printf.printf "Unknown command “%s”\n" x; parseArgs xs

let defaults = function | [] -> [Help] | xs -> xs

let rec main () =
  try Array.to_list Sys.argv |> List.tl |> parseArgs |> defaults |> List.iter cmd;
  if !repl then loop () else () with Restart -> main ()

let () = main ()
