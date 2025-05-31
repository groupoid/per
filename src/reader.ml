open Printer
open Lexing
open Exp
open Error
open Check

let parseErr f lexbuf filename =
  try f Lexer.main lexbuf
  with Parser.Error ->
    raise (Error.Parser (lexbuf.lex_curr_p.pos_lnum, lexeme lexbuf, filename))

let lex filename =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  Printf.printf "Lexing “%s”.\n" filename;
  try while true do
    let tok = Lexer.main lexbuf in
    if tok = Parser.EOF then raise End_of_file
    else print_string (Lexer.tokenToString tok ^ " ")
  done with End_of_file -> close_in chan;
  print_newline ()

let showDecl : decl -> string = function
  | Def (p, exp1, exp2) -> Printf.sprintf "def %s : %s := %s" p (showExp exp1) (showExp exp2)
  | Axiom (p, exp) -> Printf.sprintf "axiom %s : %s" p (showExp exp)

let showLine : line -> string = function
  | Import p -> Printf.sprintf "import %s" (String.concat " " p)
  | Option (opt, value) -> Printf.sprintf "option %s %s" opt value
  | Decl d -> showDecl d

let showContent x = String.concat "\n" (List.map showLine x)

let showFile : file -> string = function | (p, x) -> Printf.sprintf "module %s where\n%s" p (showContent x)

let rec checkLine st : line -> state =
  let (ctx, checked) = st in function
  | Decl d -> if !verbose then begin  Printf.printf "Checking: %s\n" (getDeclName d); flush_all () end; (checkDecl ctx (freshDecl d), checked)
  | Option (opt, value) ->
    begin match opt with
      | "irrelevance" -> irrelevance := getBoolVal opt value
      | "girard"   -> girard  := getBoolVal opt value
      | "verbose"  -> verbose := getBoolVal opt value
      | "pre-eval" -> preeval := getBoolVal opt value
      | _          -> raise (UnknownOption opt)
    end; st
  | Import xs -> List.fold_left (fun st x -> let path = ext x in
    if Files.mem path checked then st else checkFile st path) st xs

and checkFile p path =
  let (ctx, checked) = p in
  let filename = Filename.basename path in
  let chan = open_in path in
  let (name, con) = parseErr Parser.file (Lexing.from_channel chan) path in close_in chan; if !verbose then begin Printf.printf "Parsed “%s” successfully.\n" filename; flush_all () end;
  if ext name = filename then () else raise (InvalidModuleName (name, filename));
  let res = checkContent (ctx, Files.add path checked) con in print_endline ("File “" ^ filename ^ "” checked."); res

and checkContent st xs = List.fold_left checkLine st xs

let parse filename =
  let chan = open_in filename in
  Printf.printf "Parsing “%s”.\n" filename;
  Error.handleErrors
    (fun chan ->
      let lexbuf = Lexing.from_channel chan in
      let file = parseErr Parser.file lexbuf filename in
      print_endline (showFile file))
    chan ()
