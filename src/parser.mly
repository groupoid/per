%{ open Exp %}

%token <string> IDENT
%token <Z.t> KAN
%token <Z.t> PRE
%token <string> EXT
%token LPARENS RPARENS LSQ RSQ COMMA COLON IRREF EOF HOLE DEFEQ PROD ARROW DOT LAM MODULE WHERE IMPORT DEF AXIOM
%token SIGMA PI OPTION LT GT APPFORMULA PATHP TRANSP HCOMP PARTIAL PARTIALP MAP INC OUC AND OR NEGATE
%token ID REF IDJ INDEMPTY INDUNIT INDBOOL W INDW SUP
%left APPFORMULA
%left OR AND
%right ARROW PROD
%nonassoc NEGATE
%nonassoc DOT
%start <Exp.file> file
%start <Exp.command> repl

%%

ident : IRREF { Irrefutable } | IDENT { ident $1 }
vars : ident+ { $1 }
lense : LPARENS vars COLON exp2 RPARENS { List.map (fun x -> (x, $4)) $2 }
telescope : lense telescope { List.append $1 $2 } | lense { $1 }
params : telescope { $1 } | { [] }
path : IDENT { getPath $1 }
face : LPARENS IDENT IDENT IDENT RPARENS { face $2 $3 $4 }
part : face+ ARROW exp2 { ($1, $3) }
file : MODULE IDENT WHERE line* EOF { ($2, $4) }
line : IMPORT path+ { Import $2 } | OPTION IDENT IDENT { Option ($2, $3) } | declarations { Decl $1 }
repl : COLON IDENT exp2 EOF { Command ($2, $3) } | COLON IDENT EOF { Action $2 } | exp2 EOF { Eval $1 } | EOF { Nope }
exp1 : exp2 COMMA exp1 { EPair (ref None, $1, $3) } | exp2 { $1 }

exp2:
  | LAM telescope COMMA exp2 { telescope eLam $4 $2 }
  | PI telescope COMMA exp2 { telescope ePi $4 $2 }
  | SIGMA telescope COMMA exp2 { telescope eSig $4 $2 }
  | W telescope COMMA exp2 { telescope eW $4 $2 }
  | LT vars GT exp2 { pLam $4 $2 }
  | exp3 { $1 }

exp3:
  | exp3 APPFORMULA exp3 { EAppFormula ($1, $3) }
  | exp3 ARROW exp3 { impl $1 $3 }
  | exp3 PROD exp3 { prod $1 $3 }
  | exp3 AND exp3 { EAnd ($1, $3) }
  | exp3 OR exp3 { EOr ($1, $3) }
  | exp4 { $1 }

exp4 :
  | exp4 exp6 { EApp ($1, $2) }
  | ID exp6 { EId $2 }
  | REF exp6 { ERef $2 }
  | IDJ exp6 { EJ $2 }
  | INC exp6 exp6 { EInc ($2, $3) }
  | OUC exp6 { EOuc $2 }
  | PATHP exp6 { EPathP $2 }
  | TRANSP exp6 exp6 { ETransp ($2, $3) }
  | HCOMP exp6 exp6 exp6 exp6 { EHComp ($2, $3, $4, $5) }
  | PARTIAL exp6 { EPartial $2 }
  | PARTIALP exp6 exp6 { EPartialP ($2, $3) }
  | INDEMPTY exp6 { EIndEmpty $2 }
  | INDUNIT exp6 { EIndUnit $2 }
  | INDBOOL exp6 { EIndBool $2 }
  | SUP exp6 exp6 { ESup ($2, $3) }
  | INDW exp6 exp6 exp6 { EIndW ($2, $3, $4) }
  | exp5 { $1 }

exp5:
  | exp6 LSQ exp2 MAP exp2 RSQ { ESub ($1, $3, $5) }
  | exp6 { $1 }

exp6:
  | HOLE { EHole }
  | PRE { EPre $1 }
  | KAN { EKan $1 }
  | exp6 DOT IDENT { match $3 with | "1" -> EFst $1 | "2" -> ESnd $1 | field -> EField ($1, field) }
  | NEGATE exp6 { ENeg $2 }
  | LSQ separated_list(COMMA, part) RSQ { ESystem (System.of_seq (Seq.filter_map parsePartial (List.to_seq $2))) }
  | LPARENS exp1 RPARENS { $2 }
  | IDENT { getVar $1 }

declarations:
  | DEF IDENT params COLON exp2 DEFEQ exp2 { Def ($2, telescope ePi $5 $3, telescope eLam $7 $3) }
  | AXIOM IDENT params COLON exp2 { Axiom ($2, telescope ePi $5 $3) }
