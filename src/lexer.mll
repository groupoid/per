{

open Parser
open Lexing

let tokenToString : token -> string = function
  | IDENT s    -> Printf.sprintf "IDENT «%s»" s
  | PRE u      -> Printf.sprintf "PRE %s" (Z.to_string u)
  | KAN u      -> Printf.sprintf "KAN %s" (Z.to_string u)
  | EXT s      -> Printf.sprintf "EXT «%s»" s
  | DEF        -> "DEF"         | SIGMA      -> "SIGMA"
  | PI         -> "PI"          | HOLE       -> "HOLE"
  | RPARENS    -> "RPARENS"     | LPARENS    -> "LPARENS"
  | RSQ        -> "RSQ"         | LSQ        -> "LSQ"
  | LAM        -> "LAM"         | PROD       -> "PROD"
  | OPTION     -> "OPTION"      | AXIOM      -> "AXIOM"
  | IRREF      -> "IRREF"       | EOF        -> "EOF"
  | DEFEQ      -> "DEFEQ"       | COMMA      -> "COMMA"
  | COLON      -> "COLON"       | ARROW      -> "ARROW"
  | WHERE      -> "WHERE"       | MODULE     -> "MODULE"
  | LT         -> "LT"          | GT         -> "GT"
  | APPFORMULA -> "APPFORMULA"  | NEGATE     -> "NEGATE"
  | AND        -> "AND"         | OR         -> "OR"
  | PATHP      -> "PATHP"       | TRANSP     -> "TRANSP"
  | ID         -> "ID"          | REF        -> "REF"
  | PARTIAL    -> "PARTIAL"     | PARTIALP   -> "PARTIALP"
  | MAP        -> "MAP"         | IMPORT     -> "IMPORT"
  | INC        -> "INC"         | OUC        -> "OUC"
  | HCOMP      -> "HCOMP"       | DOT        -> "DOT"
  | IDJ        -> "IDJ"         | W          -> "W"
  | SUP        -> "SUP"         | INDEMPTY   -> "INDEMPTY"
  | INDUNIT    -> "INDUNIT"     | INDBOOL    -> "INDBOOL"
  | INDW       -> "INDW"

let nextLine lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = pos.pos_cnum;
                 pos_lnum = pos.pos_lnum + 1 }

let ten = Z.of_int 10

let getLevel s =
  let res = ref Z.zero in let queue = Queue.of_seq (String.to_seq s) in
  let sym = Queue.take queue in if (sym <> 'U' && sym <> 'V') then failwith "invalid universe";

  while not (Queue.is_empty queue) do
    if (Queue.take queue <> '\xE2' || Queue.take queue <> '\x82') then failwith "invalid universe level while lexing";
    let value = Char.code (Queue.take queue) - 0x80 in res := Z.add (Z.mul !res ten) (Z.of_int value) done;
    !res

}

let lat1      = [^ '\t' ' ' '\r' '\n' '(' ')' '[' ']' ':' '.' ',' '<' '>']
let beg       = lat1 # '-'
let bytes2    = ['\192'-'\223']['\128'-'\191']
let bytes3    = ['\224'-'\239']['\128'-'\191']['\128'-'\191']
let bytes4    = ['\240'-'\247']['\128'-'\191']['\128'-'\191']['\128'-'\191']
let nl        = "\r\n"|"\r"|"\n"
let inline    = "--" [^ '\n' '\r']* (nl|eof)
let utf8      = lat1|bytes2|bytes3|bytes4
let ident     = beg utf8*
let ws        = ['\t' ' ']
let defeq     = ":="  | "\xE2\x89\x94" | "\xE2\x89\x9C" | "\xE2\x89\x9D" (* ≜ | ≔ | ≜ | ≝ *)
let map       = "|->" | "\xE2\x86\xA6"          (* ↦ *)
let arrow     = "->"  | "\xE2\x86\x92"          (* → *)
let prod      = "*"   | "\xC3\x97"              (* × *)
let meet      = "/\\" | "\xE2\x88\xA7"          (* ∧ *)
let join      = "\\/" | "\xE2\x88\xA8"          (* ∨ *)
let forall    = "forall" | "\xCE\xA0" | "П"     (* Π *)
let summa     = "summa"  | "\xCE\xA3"           (* Σ *)
let lambda    = "\\" | "\xCE\xBB"               (* λ *)
let subscript = '\xE2' '\x82' ['\x80'-'\x89']
let kan       = 'U' subscript*
let pre       = 'V' subscript*
let indempty  = "ind-empty" | "ind\xE2\x82\x80" (* ind₀ *)
let indunit   = "ind-unit"  | "ind\xE2\x82\x81" (* ind₁ *)
let indbool   = "ind-bool"  | "ind\xE2\x82\x82" (* ind₂ *)
let indw      = "ind-W"     | "ind\xE1\xB5\x82" (* ind₂ *)

rule main = parse
  | nl         { nextLine lexbuf; main lexbuf }
  | inline     { nextLine lexbuf; main lexbuf }
  | "{-"       { multiline lexbuf }
  | "begin"    { ext "" lexbuf }
  | ws+        { main lexbuf }
  | kan as s   { KAN (getLevel s) } | pre as s   { PRE (getLevel s) }
  | ":"        { COLON }            | ","        { COMMA }
  | "("        { LPARENS }          | ")"        { RPARENS }
  | "["        { LSQ }              | "]"        { RSQ }
  | "<"        { LT }               | ">"        { GT }
  | "."        { DOT }              | "-"        { NEGATE }
  | defeq      { DEFEQ }            | map        { MAP }
  | forall     { PI }               | summa      { SIGMA }
  | meet       { AND }              | join       { OR }
  | arrow      { ARROW }            | prod       { PROD }
  | indempty   { INDEMPTY }         | indunit    { INDUNIT }
  | indbool    { INDBOOL }          | eof        { EOF }
  | indw       { INDW }             | "W"        { W }
  | "_"        { IRREF }            | "@"        { APPFORMULA }
  | "?"        { HOLE }             | lambda     { LAM  }
  | ident as s {
    match s with
    | "module"     -> MODULE   | "where"      -> WHERE
    | "import"     -> IMPORT   | "option"     -> OPTION
    | "PathP"      -> PATHP    | "transp"     -> TRANSP
    | "hcomp"      -> HCOMP    | "Partial"    -> PARTIAL
    | "PartialP"   -> PARTIALP | "inc"        -> INC
    | "ouc"        -> OUC      | "sup"        -> SUP
    | "def"                    | "theorem"    -> DEF
    | "axiom"                  | "postulate"  -> AXIOM
    | "Id"         -> ID       | "ref"        -> REF
    | "idJ"        -> IDJ      | _            -> IDENT s
    }

and multiline = parse
| "-}" { main lexbuf }
| nl   { nextLine lexbuf; multiline lexbuf }
| eof  { failwith "EOF in multiline comment" }
| _    { multiline lexbuf }

and ext buf = parse
| "end" { EXT buf }
| nl    { nextLine lexbuf; ext (buf ^ Lexing.lexeme lexbuf) lexbuf }
| eof   { failwith "unterminated external code" }
| _     { ext (buf ^ Lexing.lexeme lexbuf) lexbuf }

