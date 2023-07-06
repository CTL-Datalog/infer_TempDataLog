%{ open Ast_utility %}
%{ open List %}

(*%token <string> EVENT*)
%token <string> VAR
%token <int> INTE
%token EMPTY LPAR RPAR CONCAT  POWER  DISJ   
%token COLON  REQUIRE ENSURE IfStmt LSPEC RSPEC NULL
%token UNDERLINE KLEENE EOF BOTTOM NOTSINGLE RETURN
%token GT LT EQ GTEQ LTEQ CONJ COMMA MINUS 
%token PLUS TRUE FALSE 
%token FUTURE GLOBAL IMPLY LTLNOT NEXT UNTIL LILAND LILOR
%left DISJ 
%left CONCAT



%start specification
%type <(Ast_utility.specification)> specification
%type <(Ast_utility.pure)> pure
%type <(Ast_utility.basic_type)> basic_type
%type <(Ast_utility.basic_type list)> parm
%type <(Ast_utility.fact list)> factList
%type <(string list)> formalparm
%type <(Ast_utility.basic_type list)> actualparm
%type <(Ast_utility.ltl)> ltl
%type <(Ast_utility.terms)> term
%%

basic_type : 
| i = INTE{      BINT ( i)
    }
| v = VAR {BVAR v} 
| NULL {BNULL}
| RETURN {BRET}

parm:
| LPAR RPAR {[]}
| LPAR argument= basic_type RPAR {[argument]}


anyEventOrAny:
| {Any}
| p=parm { Singleton (("_", p), None) }

neGationAny:
| UNDERLINE p=parm  { NotSingleton (("_", p))}
| str = VAR p=parm { NotSingleton ((str, p))}


term:
| b = basic_type {Basic b}
| LPAR r = term RPAR { r }
| a = term b = INTE {Minus (a, Basic( BINT (0 -  b)))}
| LPAR a = term MINUS b = term RPAR {Minus (a, b )}
| LPAR a = term PLUS b = term RPAR {Plus (a, b)}


(*

pure_helper:
| GT b = term {(">", b)}
| LT b = term {("<", b)}
| GTEQ b = term {(">=", b)}
| LTEQ b = term {("<=", b)}
| EQ b = term {("=", b)}

pure_aux:
| CONJ b = pure {("conj", b)}
| DISJ b = pure {("disj", b)}

*)

pure:
| TRUE {TRUE}
| FALSE {FALSE}
| NOTSINGLE LPAR a = pure RPAR {Neg a}
| LPAR r = pure RPAR { r }
| a = term GT b = term {Gt (a, b)}
| a = term LT b = term {Lt (a, b)}
| a = term GTEQ b = term {GtEq (a, b)}
| a = term LTEQ b = term {LtEq (a, b)}
| a = term EQ b = term {Eq (a, b)}
| a = pure CONJ b = pure {PureAnd (a, b)}
| a = pure DISJ b = pure {PureOr (a, b)}

ltl : 
| str = VAR p=parm {Lable (str, p)} 
| LPAR r = ltl RPAR { r }
| NEXT p = ltl  {Next p}
| LPAR p1= ltl UNTIL p2= ltl RPAR {Until (p1, p2)}
| GLOBAL p = ltl {Global p}
| FUTURE p = ltl {Future p}
| LTLNOT p = ltl {NotLTL p}
| LPAR p1= ltl IMPLY p2= ltl RPAR {Imply (p1, p2)}
| LPAR p1= ltl LILAND p2= ltl RPAR {AndLTL (p1, p2)}  
| LPAR p1= ltl LILOR p2= ltl RPAR {OrLTL (p1, p2)}




formalparm:
| {[]}
| str = VAR {[str]}
| str = VAR COMMA rest=formalparm {str:: rest}

actualparm:
| {[]}
| str = basic_type {[str]}
| str = basic_type COMMA rest=actualparm {str:: rest}


factList: 
| str = VAR LPAR argument=actualparm RPAR {[(str, argument)]}


specification: 
| EOF {(CallStmt ("", []), [])}
| LSPEC str = VAR LPAR argument=formalparm RPAR COLON 
facts = factList RSPEC {(CallStmt (str, argument), facts)}
| LSPEC IfStmt LPAR condition =pure RPAR COLON 
facts = factList RSPEC {(IfStmt (condition), facts)}





