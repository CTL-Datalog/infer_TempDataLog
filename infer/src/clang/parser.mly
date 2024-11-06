%{ open Ast_utility %}
%{ open List %}

(*%token <string> EVENT*)
%token <string> VAR
%token <int> INTE
%token LPAR RPAR  DISJ   
%token LSPEC RSPEC NULL
%token EOF NOTSINGLE RETURN
%token GT LT EQ GTEQ LTEQ CONJ COMMA MINUS  CTLCONJ
%token PLUS TRUE FALSE AX EX AF EF AG EG AU EU
%token IMPLY 
%left DISJ 



%start ctl
%type <(Ast_utility.ctl)> ctl
%type <(Ast_utility.pure)> pure
%type <(Ast_utility.basic_type)> basic_type
%type <(Ast_utility.terms)> term
%%

basic_type : 
| i = INTE{      BINT ( i)
    }
| v = VAR {BSTR v} 
| NULL {BNULL}
| RETURN {BRET}



term:
| b = basic_type {Basic b}
| LPAR r = term RPAR { r }
| a = term b = INTE {Minus (a, Basic( BINT (0 -  b)))}
| LPAR a = term MINUS b = term RPAR {Minus (a, b )}
| LPAR a = term PLUS b = term RPAR {Plus (a, b)}




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
| str= VAR LPAR tLi=separated_list(COMMA, term) RPAR {Predicate (str, tLi)}





ctl_formula:
| p =pure {

  let string_of_int_shall n = 
    if n >= 0 then string_of_int n 
    else "neg_" ^ string_of_int (-1 * n)
  in 

  let rec propositionName pi : (string * pure) = 
    match pi with 
    | Eq (Basic(BSTR str), Basic(BINT n)) -> str ^ "_eq_" ^ string_of_int_shall n, (Eq (Basic(BSTR str), Basic(BINT n)))
    | Eq (Basic(BSTR str), Basic(BSTR str1)) -> str ^ "_eq_" ^ str1, (Eq (Basic(BSTR str), Basic(BSTR str1)))

    | Gt (Basic(BSTR str), Basic(BINT n)) -> str ^ "_gt_" ^ string_of_int_shall n, (Gt (Basic(BSTR str), Basic(BINT n)))
    | Gt (Basic(BSTR str), Basic(BSTR str1)) -> str ^ "_gt_" ^ str1, (Gt (Basic(BSTR str), Basic(BSTR str1)))

    | Lt (Basic(BSTR str), Basic(BINT n)) -> str ^ "_lt_" ^ string_of_int_shall n, (Lt (Basic(BSTR str), Basic(BINT n)))
    | Lt (Basic(BSTR str), Basic(BSTR str1)) -> str ^ "_lt_" ^ str1, (Lt (Basic(BSTR str), Basic(BSTR str1)))

    | GtEq (Basic(BSTR str), Basic(BINT n)) -> str ^ "_gteq_" ^ string_of_int_shall n, (GtEq (Basic(BSTR str), Basic(BINT n)))
    | GtEq (Basic(BSTR str), Basic(BSTR str1)) -> str ^ "_gteq_" ^ str1, (GtEq (Basic(BSTR str), Basic(BSTR str1)))

    | LtEq (Basic(BSTR str), Basic(BINT n)) -> str ^ "_lteq_" ^ string_of_int_shall n, (LtEq (Basic(BSTR str), Basic(BINT n)))
    | LtEq (Basic(BSTR str), Basic(BSTR str1)) -> str ^ "_lteq_" ^ str1, (LtEq (Basic(BSTR str), Basic(BSTR str1)))

    | PureAnd (pi1, pi2) -> 
      let n1, p1 = propositionName pi1 in 
      let n2, p2 = propositionName pi2 in 
      n1 ^ "_and_" ^ n2, PureAnd (p1, p2)

    | PureOr (pi1, pi2) -> 
      let n1, p1 = propositionName pi1 in 
      let n2, p2 = propositionName pi2 in 
      n1 ^ "_or_" ^ n2, PureOr (p1, p2)

    | Neg (pi1) -> let n1, p1 = propositionName pi1 in 
      "not_" ^ n1, Neg (p1)


    | Predicate (str, termLi) -> str, (Predicate (str, termLi))
    | _ -> "propositionDefult " ^ string_of_pure pi, pi
  in  
  Atom(propositionName p)}

| LPAR ctl = ctl_formula RPAR {ctl}
| NOTSINGLE ctl = ctl_formula {(Neg ctl)}
| AX LPAR ctl = ctl_formula RPAR {(AX ctl)}
| EX LPAR ctl = ctl_formula RPAR {(EX ctl)}
| AF LPAR ctl = ctl_formula RPAR {(AF ctl)}
| EF LPAR ctl = ctl_formula RPAR {(EF ctl)}
| AG LPAR ctl = ctl_formula RPAR {(AG ctl)}
| EG LPAR ctl = ctl_formula RPAR {(EG ctl)}
| AU LPAR ctl1 = ctl_formula COMMA ctl2 = ctl_formula RPAR {AU(ctl1, ctl2)}
| EU LPAR ctl1 = ctl_formula COMMA ctl2 = ctl_formula RPAR {EU(ctl1, ctl2)}
| ctl1 = ctl_formula CTLCONJ ctl2 = ctl_formula {Conj(ctl1, ctl2)}
| ctl1 = ctl_formula DISJ ctl2 = ctl_formula {Disj(ctl1, ctl2)}
| ctl1 = ctl_formula IMPLY ctl2 = ctl_formula {Imply(ctl1, ctl2)}


ctl: 
| EOF {Atom("propositionDefult", TRUE)}
| LSPEC 
  ctl_formula  = ctl_formula

  RSPEC {ctl_formula}
