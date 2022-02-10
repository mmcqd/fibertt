%{

module List = Core.List
open Raw

%}


%token EOF
%token LPAREN RPAREN LSQAURE RSQUARE LCURLY RCURLY
%token LAMBDA R_ARROW R_EQ_ARROW
%token TELE
%token SUB
%token STAR COMMA DOT1 DOT2
%token TYPE
%token ELIM BAR FSLASH
%token DATA
%token UNDERBAR HOLE
%token COLON
%token DEF AXIOM IMPORT
%token <string> IDENT

%right R_ARROW
%right STAR

%type <cmd list> init

%start init

%% 

let loc(x) := 
  | x = x; { {con = x ; loc = $loc} }

let paren(x) == LPAREN; ~ = x; RPAREN; <>

let var :=
  | UNDERBAR ; { "_" }
  | x = IDENT; { x }

let init := ~ = nonempty_list(cmd); EOF; <>

let cmd :=
  | ~ = term; <Eval>
  | DEF; name = var; R_EQ_ARROW; tm = term; { Def {name ; tm} }
  | DEF; name = var; COLON; tp = term; R_EQ_ARROW; tm = term; { DefChk {name ; tm ; tp} }
  | DEF; name = var; doms = tele; COLON; ran = term; R_EQ_ARROW; body = term; { DefFun {name ; doms ; ran ; body} }
  | IMPORT; ~ = IDENT; <Import>

let tele :=
  | list(tele_arg)

let tele_arg :=
  | TELE; LPAREN; xs = list(var); COLON; tp = term; RPAREN; { (xs,tp) }

let lam_arg :=
  | var

let spine :=
  | xs = spine_; { List.rev xs }

let spine_ :=
  | x = lam_term; { [x] }
  | x = atom; { [x] }
  | x = atom; xs = spine_; { x :: xs }

let term := loc(term_)
let term_ := 
  | atom_
  | f = atom; xs = spine; { Ap (f,xs) }
  | dom = term; R_ARROW; ran = term; { Pi ([(["_"],dom)], ran) }
  | doms = tele; R_ARROW; ran = term; { Pi (doms,ran) }
  | SUB; tp = atom; tm = atom; { Singleton {tm ; tp} }
  | lam_term_

let lam_term := loc(lam_term_)
let lam_term_ :=
  | LAMBDA; xs = nonempty_list(lam_arg); R_EQ_ARROW; e = term; <Lam>

let atom == loc(atom_)
let atom_ :=
  | TYPE; { U }
  | ~ = IDENT; <Var>
  | paren(term_)