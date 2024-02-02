open Z3

let flowKeyword = "flow"
let valueKeyword = "valuation"
let retKeyword = "Return"
let joinKeyword = "Join"
let entryKeyWord = "Start"
let assignKeyWord = "Assign"
let stateKeyWord = "State"
let locKeyWord = "loc"
let loc_inter_KeyWord = "locI"
let transFlowKeyWord = "transFlow"
let outputShellKeyWord = "_Final"
let joinNodeKeyWord ="Join"
let leqKeyWord = "LtEq"

let nonDetermineFunCall = ["_fun__nondet_int";"_fun___VERIFIER_nondet_int"]


type basic_type = BINT of int | BVAR of string | BNULL | BRET | ANY | BSTR of string

type event = string * (basic_type list)

type state = int

type bindings = (string * basic_type) list


type terms = Basic of basic_type 
           | Plus of terms * terms
           | Minus of terms * terms 
       
(*Arithimetic pure formulae*)
type pure = TRUE
          | FALSE
          | Gt of terms * terms
          | Lt of terms * terms
          | GtEq of terms * terms
          | LtEq of terms * terms
          | Eq of terms * terms
          | PureOr of pure * pure
          | PureAnd of pure * pure
          | Neg of pure
          | Predicate of (string * terms list)

type fact = (string *  (basic_type list)) 
type facts = fact list
type reachableState = int list 

type transitionSummary = (pure * ((terms * terms)list)) list


(* facts is the abstract interpretation, 
the first int is the exit code, and the reachableState is the most recent pre-states *)
type programState = (facts * int * reachableState)

type programStates = (programState list)

type mnsigniture = (string *  (string list))

type stmtPattern = IfStmt of pure | CallStmt of mnsigniture

type specification = (stmtPattern * fact list)

type stack = (Exp.t * Ident.t) list


type regularExpr = 
  | Bot 
  | Emp 
  | Singleton of (pure * state)
  | Disjunction of (regularExpr * regularExpr)
  | Concate of (regularExpr * regularExpr)
  | Kleene of regularExpr
  | Omega of regularExpr 
  | Guard of (pure * state)

type fstElem = 
    PureEv of (pure * state) 
  | GuardEv of (pure * state) 
  | KleeneEv of regularExpr
  | OmegaEv of regularExpr

type reCFG  = (Procdesc.Node.t list * stack)

type propositions = string * pure

type ctl = 
    Atom of propositions 
  | Neg of ctl 
  | Conj of ctl * ctl 
  | Disj of ctl * ctl 
  | Imply of ctl * ctl 
  | AX of ctl 
  | EX of ctl 
  | AF of ctl 
  | EF of ctl 
  | AG of ctl 
  | EG of ctl 
  | AU of ctl * ctl 
  | EU of ctl * ctl 




(* Global States *)
let (varSet: (string list) ref) = ref [] 
let (handlerVar: string option ref) = ref None 

(* Experimental Summary *)
let allTheUniqueIDs = ref (-1)
let totol_execution_time  = ref 0.0
let totol_Lines_of_Code  = ref 0
let totol_Lines_of_Spec  = ref 0
let currentFunctionLineNumber = ref (0, 0) 


let (totol_specifications: (ctl list) ref)  = ref []


let rec flattenList lili = 
  match lili with 
  | [] -> []
  | x :: xs -> List.append x (flattenList xs) 

  
let rec iter f = function
  | [] -> ()
  | [x] ->
      f true x
  | x :: tl ->
      f false x;
      iter f tl

let to_buffer ?(line_prefix = "") ~get_name ~get_children buf x =
  let rec print_root indent x =
    bprintf buf "%s\n" (get_name x);
    let children = get_children x in
    iter (print_child indent) children
  and print_child indent is_last x =
    let line =
      if is_last then
        "└── "
      else
        "├── "
    in
    bprintf buf "%s%s" indent line;
    let extra_indent =
      if is_last then
        "    "
      else
        "│   "
    in
    print_root (indent ^ extra_indent) x
  in
  Buffer.add_string buf line_prefix;
  print_root line_prefix x

let printTree ?line_prefix ~get_name ~get_children x =
  let buf = Buffer.create 1000 in
  to_buffer ?line_prefix ~get_name ~get_children buf x;
  Buffer.contents buf

let takefst (a ,_) = a
type binary_tree =
  | Node of string * (binary_tree  list )
  | Leaf

let get_name = function
    | Leaf -> "."
    | Node (name, li) -> name;;

let get_children = function
    | Leaf -> []
    | Node (_, li) -> List.filter ~f:(fun a ->
      match a with 
      | Leaf -> false 
      | _ -> true ) li;;


let string_of_basic_t v = 
  match v with 
  | BVAR name -> name
  | BINT n -> string_of_int n
  | BNULL -> "NULL"
  | BRET -> "ret"
  | ANY -> "_"
  | BSTR s -> "\"" ^ s ^ "\""



let string_of_loc n = "@" ^ string_of_int n


let argumentsTerms2basic_types (t: (terms option) list): (basic_type list) = 
  List.fold_left t ~init:[] ~f:(fun acc a ->
    match a with 
    | Some (Basic (BVAR str)) -> List.append acc [(BVAR str)]
    | _ -> acc 
  )


let rec string_of_terms (t:terms):string = 
  match t with
  | Basic v -> string_of_basic_t v 
  | Plus (t1, t2) -> (string_of_terms t1) ^ ("+") ^ (string_of_terms t2)
  | Minus (t1, t2) -> (string_of_terms t1) ^ ("-") ^ (string_of_terms t2)


let string_of_termOption t : string option  = 
  match t with 
  | None -> None 
  | Some t -> Some (string_of_terms t)

let rec string_of_list_terms tL: string = 
  match tL with 
  | [] -> ""
  | [t] -> string_of_terms t 
  | x :: xs ->  string_of_terms x ^", "^ string_of_list_terms xs 

let rec string_of_pure (p:pure):string =   
  match p with
    TRUE -> "⊤"
  | FALSE -> "⊥"
  | Gt (t1, t2) -> (string_of_terms t1) ^ ">" ^ (string_of_terms t2)
  | Lt (t1, t2) -> (string_of_terms t1) ^ "<" ^ (string_of_terms t2)
  | GtEq (t1, t2) -> (string_of_terms t1) ^ ">=" ^ (string_of_terms t2) (*"≥"*)
  | LtEq (t1, t2) -> (string_of_terms t1) ^ "<=" ^ (string_of_terms t2) (*"≤"*)
  | Eq (t1, t2) -> (string_of_terms t1) ^ "=" ^ (string_of_terms t2)
  | PureOr (p1, p2) -> "("^string_of_pure p1 ^ "∨" ^ string_of_pure p2^")"
  | PureAnd (p1, p2) -> string_of_pure p1 ^ "∧" ^ string_of_pure p2
  | Neg (Eq (t1, t2)) -> "("^(string_of_terms t1) ^ "!=" ^ (string_of_terms t2)^")"
  | Neg (Gt (t1, t2)) -> "("^(string_of_terms t1) ^ "<=" ^ (string_of_terms t2)^")"

  | Neg p -> "!(" ^ string_of_pure p^")"
  | Predicate (str, termLi) -> str ^ "(" ^ string_of_list_terms termLi ^ ")"



let rec string_of_transitionSummary (su:transitionSummary) : string = 
  (String.concat ~sep:";\n" (List.map ~f:(fun (x,y) -> 
    string_of_pure x ^ " /\\ " ^  
    (String.concat ~sep:" , " ((List.map ~f:(fun (t1, t2) -> string_of_terms t1 ^"->"^ string_of_terms t2 ) y)))
  ) su))


let rec string_of_ctl (ctl:ctl) = 
  match ctl with
  | Atom (s, p) -> s ^  string_of_pure p 
  | Neg c -> "!(" ^ string_of_ctl c ^")"
  | Conj (c1, c2) -> "(" ^ string_of_ctl c1 ^" /\\ "^ string_of_ctl c2 ^")"
  | Disj (c1, c2) -> "(" ^ string_of_ctl c1 ^" \\/ "^ string_of_ctl c2 ^")"
  | Imply (c1, c2) -> "(" ^ string_of_ctl c1 ^" => "^ string_of_ctl c2 ^")"
  | AX c -> "AX(" ^ string_of_ctl c ^")"
  | EX c -> "EX(" ^ string_of_ctl c ^")"
  | AF c -> "AF(" ^ string_of_ctl c ^")"
  | EF c -> "EF(" ^ string_of_ctl c ^")"
  | AG c -> "AG(" ^ string_of_ctl c ^")"
  | EG c -> "EG(" ^ string_of_ctl c ^")"
  | AU (c1, c2) -> "AU(" ^ string_of_ctl c1 ^","^ string_of_ctl c2 ^")"
  | EU (c1, c2) -> "EU(" ^ string_of_ctl c1 ^","^ string_of_ctl c2 ^")"
 


let rec string_of_pure_output (p:pure):string =   
  match p with
    TRUE -> "⊤"
  | FALSE -> "⊥"
  | Gt (t1, t2) -> (string_of_terms t1) ^ ">" ^ (string_of_terms t2)
  | Lt (t1, t2) -> (string_of_terms t1) ^ "<" ^ (string_of_terms t2)
  | GtEq (t1, t2) -> (string_of_terms t1) ^ ">=" ^ (string_of_terms t2)
  | LtEq (t1, t2) -> (string_of_terms t1) ^ "<=" ^ (string_of_terms t2)
  | Eq (t1, t2) -> (string_of_terms t1) ^ "==" ^ (string_of_terms t2)
  | PureOr (p1, p2) -> "("^string_of_pure_output p1 ^ "∨" ^ string_of_pure_output p2^")"
  | PureAnd (p1, p2) -> string_of_pure_output p1 ^ "∧" ^ string_of_pure_output p2
  | Neg (Eq (t1, t2)) -> "("^(string_of_terms t1) ^ "!=" ^ (string_of_terms t2)^")"
  | Neg p -> "!(" ^ string_of_pure_output p^")"
  | Predicate (str, termLi) -> str ^ "(" ^ string_of_list_terms termLi ^ ")"



let rec string_of_regularExpr re = 
  match re with 
  | Bot              -> "⏊"
  | Emp              -> "𝝐 " 
  | Singleton (p, state)  -> "(" ^string_of_pure p  ^ ")"^ string_of_loc state
  | Concate (eff1, eff2) -> string_of_regularExpr eff1 ^ " · " ^ string_of_regularExpr eff2 
  | Disjunction (eff1, eff2) ->
      "((" ^ string_of_regularExpr eff1 ^ ") \\/ (" ^ string_of_regularExpr eff2 ^ "))"
  | Kleene effIn          ->
      "(" ^ string_of_regularExpr effIn ^ ")^*"
     
  | Omega effIn          ->
      "(" ^ string_of_regularExpr effIn ^ ")^w"

  | Guard (p, state) -> "[" ^ string_of_pure p^ "]" ^ string_of_loc state (*^ string_of_regularExpr effIn*)

let compareBasic_type (bt1:basic_type) (bt2:basic_type) : bool = 
  match (bt1, bt2) with 
  | (BSTR s1, BSTR s2)
  | ((BVAR s1), (BVAR s2)) -> String.compare s1 s2 == 0
  | (BINT n1, BINT n2) -> if n1 - n2 == 0 then true else false  
  | (BNULL, BNULL)
  | (ANY, ANY)
  | (BRET, BRET) -> true 
  | _ -> false 

let rec stricTcompareTerm (term1:terms) (term2:terms) : bool = 
  match (term1, term2) with 
  | (Basic t1, Basic t2) -> compareBasic_type t1 t2
  | (Plus (tIn1, num1), Plus (tIn2, num2)) -> stricTcompareTerm tIn1 tIn2 && stricTcompareTerm num1  num2
  | (Minus (tIn1, num1), Minus (tIn2, num2)) -> stricTcompareTerm tIn1 tIn2 && stricTcompareTerm num1  num2
  | _ -> false 

let rec compareTermList tl1 tl2 : bool = 
  match tl1, tl2 with 
  | [], [] -> true 
  | (x:: xs, y:: ys) -> stricTcompareTerm x y && compareTermList xs ys 
  | _ -> false 


let rec comparePure (pi1:pure) (pi2:pure):bool = 
  match (pi1 , pi2) with 
    (TRUE, TRUE) -> true
  | (FALSE, FALSE) -> true 
  | (Gt (t1, t11), Gt (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (Lt (t1, t11), Lt (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (GtEq (t1, t11), GtEq (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (LtEq (t1, t11), LtEq (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (Eq (t1, t11), Eq (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (PureOr (p1, p2), PureOr (p3, p4)) ->
      (comparePure p1 p3 && comparePure p2 p4) || (comparePure p1 p4 && comparePure p2 p3)
  | (PureAnd (p1, p2), PureAnd (p3, p4)) ->
      (comparePure p1 p3 && comparePure p2 p4) || (comparePure p1 p4 && comparePure p2 p3)
  | (Neg p1, Neg p2) -> comparePure p1 p2
  | (Predicate (s1, tLi1), Predicate (s2, tLi2)) -> 
    String.compare s1 s2 == 0  &&  compareTermList tLi1 tLi2
  | _ -> false



let rec nullable (eff:regularExpr) : bool = 
  match eff with 
  | Bot              -> false 
  | Emp            -> true 
  | Singleton _ -> false
  | Guard _     -> false 
  | Concate (eff1, eff2) -> nullable eff1 && nullable eff2  
  | Disjunction (eff1, eff2) -> nullable eff1 || nullable eff2  
  | Kleene _      -> true
  | Omega _       -> false 
   
let string_of_fst_event (ele:fstElem) : string = 
  match ele with 
  | PureEv (p, s) -> string_of_pure p ^ string_of_loc s 
  | GuardEv (p, s) -> "[" ^string_of_pure p ^ "]" ^ string_of_loc s 
  | KleeneEv re -> "(" ^ string_of_regularExpr re ^ ")^*"
  | OmegaEv re -> "(" ^ string_of_regularExpr re ^ ")^w"

let rec fst (eff:regularExpr) : (fstElem list) = 
  match eff with 
  | Bot             -> []   
  | Emp  -> []
  | Singleton s     -> [(PureEv s)]
  | Guard s         -> [(GuardEv s)]
  | Concate (eff1, eff2) -> 
    if nullable eff1 then  (fst eff1) @  (fst eff2)
    else (fst eff1)
  | Disjunction (eff1, eff2) -> List.append (fst eff1) (fst eff2)
  | Kleene effIn      -> [KleeneEv effIn]
  | Omega effIn -> [OmegaEv effIn]

let rec cycleTrace (eff:regularExpr) : bool = 
  match eff with 
  | Concate (eff1, eff2) -> cycleTrace eff2
  | Disjunction (eff1, eff2) -> raise(Failure "cycleTrace has a dijunction")
  | Kleene effIn      
  | Omega effIn -> true
  | _ -> false 


let rec reverse (eff:regularExpr) :regularExpr = 
  match eff with 
  | Bot  
  | Emp  
  | Singleton _ 
  | Guard _ -> eff
  | Concate (eff1, eff2) -> Concate (reverse eff2, reverse eff1)    
  | Disjunction (eff1, eff2) -> Disjunction (reverse eff1, reverse eff2)    
  | Kleene effIn      -> Kleene (reverse effIn)
  | Omega effIn  -> Omega (reverse effIn)

let rec getStatesFromFstEle (li:fstElem list): int list  = 
  match li with 
  | [] -> [] 
  | x :: xs  -> 
    (match x with 
    | PureEv  (_, s) 
    | GuardEv (_, s) -> [s] 
    | _ -> []
    ) @ getStatesFromFstEle xs 

let rec compareRE re1 re2 : bool = 
  match (re1, re2) with 
  | (Bot, Bot) -> true 
  | (Emp, Emp) -> true 
  | (Singleton (p1, s1), Singleton (p2, s2)) 
  | (Guard (p1, s1), Guard (p2, s2))  -> 
    comparePure p1 p2 && s1 == s2
  | (Disjunction (eff1, eff2), Disjunction (eff3, eff4)) 
  | (Concate (eff1, eff2), Concate (eff3, eff4)) ->  
    compareRE eff1 eff3 && compareRE eff2 eff4
  | (Omega effIn, Omega effIn2)
  | (Kleene effIn, Kleene effIn2) -> compareRE effIn effIn2
  | _ -> false  

let compareEvent (ev1:fstElem) (ev2:fstElem) : bool  = 
  match (ev1, ev2) with 
  | (PureEv (p1, s1), PureEv(p2, s2))
  | (GuardEv (p1, s1), GuardEv(p2, s2)) -> comparePure p1 p2 && s1 == s2 
  | (OmegaEv re1, OmegaEv re2)
  | (KleeneEv re1, KleeneEv re2) -> compareRE re1 re2
  | _ -> false 

let rec existAux f (li:('a list)) (ele:'a) = 
    match li with 
    | [] ->  false 
    | x :: xs -> if f x ele then true else existAux f xs ele

let removeRedundant (fset:('a list)) (f:'a -> 'a -> bool) : ('a list) = 
  let rec helper (li:('a list)) = 
    match li with 
    | [] -> []
    | y:: ys -> if existAux f ys y then helper ys else y :: (helper ys)

  in helper fset


let rec derivitives (f:fstElem) (eff:regularExpr) : regularExpr = 
  match eff with 
  | Bot        
  | Emp -> Bot    
  | Singleton (p1, s1) -> 
    (match f with 
    | PureEv (p2, s2) -> if comparePure p1 p2 && s1 == s2 then Emp else Bot
    | _ -> Bot 
    )
  | Guard (p1, s1) -> 
    (match f with 
    | GuardEv (p2, s2) -> if comparePure p1 p2 && s1 == s2 then Emp else Bot
    | _ -> Bot 
    )
  | Concate (eff1, eff2) -> 
    let forsure = Concate (derivitives f eff1, eff2) in 
    if nullable eff1 then  Disjunction (forsure, derivitives f eff2)
    else forsure
  | Disjunction (eff1, eff2) -> 
    Disjunction (derivitives f eff1, derivitives f eff2)
  | Omega effIn | Kleene effIn      -> 
    (match f with 
    | KleeneEv (effIn1) -> if compareRE effIn effIn1 then Emp else Bot
    | _ -> Bot 
    )


let eventToRe (ev:fstElem) : regularExpr = 
  match ev with 
  | PureEv s -> Singleton s 
  | GuardEv s -> Guard s 
  | KleeneEv re -> Kleene re
  | OmegaEv re -> Omega re


let rec findTheFirstJoint (re:regularExpr) : (int * regularExpr * regularExpr) option = 
    (match fst re with 
    | [f] -> 
      (match f with 
      | PureEv (Predicate (s, _), state) -> 
        if String.compare joinKeyword s == 0 then 
          let deriv = (derivitives f re) in 
          Some (state, Emp, deriv)
        else 
          let deriv = (derivitives f re) in 
          (match findTheFirstJoint deriv with 
          | None  -> None 
          | Some (a, b, c) -> Some (a, Concate (eventToRe f, b), c)
          )

      | _ -> 
        let deriv = (derivitives f re) in 
        (match findTheFirstJoint deriv with 
        | None  -> None 
        | Some (a, b, c) -> Some (a, Concate (eventToRe f, b), c)
        )

      )
    | _ -> None )

let rec deleteAllTheJoinNodes (re:regularExpr) : regularExpr = 
  match re with 
  | Singleton (Predicate (s, _), state) -> 
    if String.compare s joinNodeKeyWord == 0 then Emp else re 
  | Kleene (reIn) -> Kleene (deleteAllTheJoinNodes reIn)
  | Disjunction(r1, r2) -> Disjunction(deleteAllTheJoinNodes r1, deleteAllTheJoinNodes r2)
  | Concate (r1, r2) -> Concate(deleteAllTheJoinNodes r1, deleteAllTheJoinNodes r2)
  | _ -> re

  ;;

let normalise_terms (t:terms) : terms = 
  match t with 
  | Minus (t1, Minus (t2, t3)) -> 
    if stricTcompareTerm t1 t2 then t3 
    else t 
  | _ -> t 

let rec normalise_pure (pi:pure) : pure = 
  match pi with 
  | TRUE 
  | FALSE -> pi
  | Gt (t1, t2) -> Gt (normalise_terms t1, normalise_terms t2)
  | Lt (t1, t2) -> Lt (normalise_terms t1, normalise_terms t2)
  | GtEq (t1, t2) -> GtEq (normalise_terms t1, normalise_terms t2)
  | LtEq (t1, t2) -> LtEq (normalise_terms t1, normalise_terms t2)
  | Eq (t1, t2) -> Eq (normalise_terms t1, normalise_terms t2)
  | PureAnd (pi1,pi2) -> PureAnd (normalise_pure pi1, normalise_pure pi2)
  | Neg piN -> Neg (normalise_pure piN)
  | PureOr (pi1,pi2) -> PureAnd (normalise_pure pi1, normalise_pure pi2)
  | Predicate (str, termLi) -> 
    Predicate (str, List.map termLi ~f:(normalise_terms))


let rec normalise_es (eff:regularExpr) : regularExpr = 
  match eff with 
  | Disjunction(es1, es2) -> 
    let es1 = normalise_es es1 in 
    let es2 = normalise_es es2 in 
    (match (es1, es2) with 
    | (Emp, Emp) -> Emp
    | (Emp, _) -> if nullable es2 then es2 else (Disjunction (es2, es1))
    | (Bot, es) -> normalise_es es 
    | (es, Bot) -> normalise_es es 
    | _ -> (Disjunction (es1, es2))
    )
  | Concate (es1, es2) -> 
    let es1 = normalise_es es1 in 
    let es2 = normalise_es es2 in 
    (match (es1, es2) with 
    | (Emp, _) -> normalise_es es2
    | (_, Emp) -> normalise_es es1
    | (Bot, _) -> Bot
    | (_, Bot) -> Bot
    | (Omega _, _) -> es1
    | (Disjunction (es11, es12), es3) -> Disjunction(normalise_es (Concate (es11,es3)),  normalise_es (Concate (es12, es3))) 
    | (Concate (es11, es12), es3) -> (Concate (es11, normalise_es (Concate (es12, es3))))
    | _ -> (Concate (es1, es2))
    )
  | Kleene effIn -> 
    let effIn' = normalise_es effIn in 
    (match effIn' with 
    | Emp -> Emp 
    | _ ->  
    Kleene (effIn'))
  | _ -> eff 



let rec varFromTerm (t:terms): string list =   
  match t with
  | Basic (BVAR v) -> [v]
  | Plus (t1, t2) 
  | Minus (t1, t2) ->  List.append (varFromTerm t1) (varFromTerm t2)
  | _ -> []

let string_of_varSet (li: string list) : string = 
  (List.fold_left li ~init:"" ~f:(fun acc a -> acc ^ "," ^ a)) ^ "\n"

let twoStringSetOverlap (sli1) (sli2) = 
  let rec helper str li = 
    match li with 
    | [] -> false 
    | x :: xs -> if String.compare x str == 0 then true else helper str xs 
  in 
  let rec aux li = 
    match li with 
    | [] -> false 
    | y :: ys -> if helper y sli2 then true else aux ys
  in aux sli1
 
let rec varFromPure (p:pure): string list =   
    match p with
    TRUE -> []
  | FALSE -> []
  | Gt (t1, t2) 
  | Lt (t1, t2) 
  | GtEq (t1, t2) 
  | LtEq (t1, t2) 
  | Eq (t1, t2) -> List.append (varFromTerm t1) (varFromTerm t2)
  | PureOr (p1, p2) 
  | PureAnd (p1, p2) -> List.append (varFromPure p1) (varFromPure p2)
  | Neg p -> varFromPure p 
  | Predicate (_, termLi) -> List.fold_left termLi ~init:[] ~f:(fun acc t -> acc @ varFromTerm t)





let rec findRetFromBindings (bt:bindings) (str: string) : basic_type option =
  match bt with
  | [] -> None 
  | (formal, artual) :: xs -> 
    if String.compare formal str == 0 then Some artual else findRetFromBindings xs str
  

let rec findRetFromBindingsRet (bt:bindings) : string option =
  match bt with
  | [] -> None 
  | (formal, BRET) :: xs -> Some formal 
  | x :: xs -> findRetFromBindingsRet xs 



let instantiateRet_basic_type (bt:basic_type) (bds:bindings):  basic_type = 
  match bt with 
  | BRET -> 
    (match findRetFromBindingsRet bds with
    | None -> bt
    | Some handler -> BVAR handler
    )
  | BVAR str -> 
    (match findRetFromBindings bds str with
    | None -> bt
    | Some term ->  term 
    )
  | _ -> bt 

let instantiateFacts (factSchema: fact list) (bds:bindings) : fact list = 
  (*let () = print_string ("instantiateRet: " ^ string_of_effect eff^ "\n") in *)
  List.map factSchema ~f:(fun (predicate_Name, args) -> 
    (predicate_Name, List.map args ~f:(fun a -> instantiateRet_basic_type a bds))) 
  (*let () = print_string ("instantiateRet after : " ^ string_of_effect temp^ "\n") in *)

(**********************************************)
exception FooAskz3 of string

let rec convertTerm (t:terms):string = 
  match t with
  | (Basic (BVAR name)) -> " " ^ name ^ " "
  | (Basic (BINT n)) -> " " ^ string_of_int n ^ " "
  | (Basic BRET) -> "ret"
  | (Basic (BNULL)) -> " " ^ "nil" ^ " "
  | Plus (t1, t2) -> ("(+") ^ (convertTerm t1) ^  (convertTerm t2) ^ ")"
  | Minus (t1, t2) -> ("(-") ^ (convertTerm t1) ^  (convertTerm t2) ^ ")"
  | Basic (BSTR _)
  | Basic ANY -> raise (Failure "convertTerm not yet")
  ;;

let rec convertPure (pi:pure) (acc:string):string = 
  match pi with
    TRUE -> "(< 0 1)"
  | FALSE -> "(> 0 1)"
  | Gt (t1, t2) -> 
      let temp1 = convertTerm t1 in
      let temp2 = convertTerm t2 in
      acc ^ "(>" ^ temp1 ^ temp2 ^")"
  | Lt (t1, t2) -> 
      let temp1 = convertTerm t1 in
      let temp2 = convertTerm t2 in
      acc ^ "(<" ^ temp1 ^ temp2 ^")"
  | GtEq (t1, t2) -> 
      let temp1 = convertTerm t1 in
      let temp2 = convertTerm t2 in
      acc ^ "(>=" ^ temp1 ^ temp2 ^")"
  | LtEq (t1, t2) -> 
      let temp1 = convertTerm t1 in
      let temp2 = convertTerm t2 in
      acc ^ "(<=" ^ temp1 ^ temp2 ^")"
  | Eq (t1, t2) -> 
      let temp1 = convertTerm t1 in
      let temp2 = convertTerm t2 in
      acc ^ "(=" ^ temp1 ^ temp2 ^")"
  | PureAnd (pi1,pi2) -> 
      let temp1 = convertPure pi1 "" in
      let temp2 = convertPure pi2 "" in
      acc ^ "(and" ^temp1 ^ temp2 ^ ")"
  | Neg piN -> 
      let temp1 = convertPure piN "" in
      acc ^ "(not" ^temp1 ^ ")"
  | PureOr (pi1,pi2) -> 
      let temp1 = convertPure pi1 "" in
      let temp2 = convertPure pi2 "" in
      acc ^ "(or" ^temp1 ^ temp2 ^ ")"
  | Predicate (str, termLi) -> raise (Failure "to z3 not yet for predicate")

      ;;




let rec getAllVarFromTerm (t:terms) (acc:string list):string list = 
  match t with
| Basic (BVAR name) -> List.append acc [name]
| Plus (t1, t2) -> 
    let cur = getAllVarFromTerm t1 acc in 
    getAllVarFromTerm t2 cur
| Minus (t1, t2) -> 
    let cur = getAllVarFromTerm t1 acc in 
    getAllVarFromTerm t2 cur
| _ -> acc
;;

let rec getAllNumFromTerm (t:terms):int list = 
  match t with
| Basic (BINT n) -> [n]
| Minus (t1, t2) 
| Plus (t1, t2) -> getAllNumFromTerm t1 @ getAllNumFromTerm t2
| _ -> []
;;




let rec getAllVarFromPure (pi:pure) (acc:string list):string list = 
  match pi with
    TRUE -> acc
  | FALSE -> acc
  | Gt (term1, term2) -> 
      let allVarFromTerm1 = getAllVarFromTerm term1 [] in
      let allVarFromTerm2 = getAllVarFromTerm term2 [] in
      List.append acc (List.append allVarFromTerm1 allVarFromTerm2)
  | Lt (term1, term2) -> 
      let allVarFromTerm1 = getAllVarFromTerm term1 [] in
      let allVarFromTerm2 = getAllVarFromTerm term2 [] in
      List.append acc (List.append allVarFromTerm1 allVarFromTerm2)
  | GtEq (term1, term2) -> 
      let allVarFromTerm1 = getAllVarFromTerm term1 [] in
      let allVarFromTerm2 = getAllVarFromTerm term2 [] in
      List.append acc (List.append allVarFromTerm1 allVarFromTerm2)
  | LtEq (term1, term2) -> 
      let allVarFromTerm1 = getAllVarFromTerm term1 [] in
      let allVarFromTerm2 = getAllVarFromTerm term2 [] in
      List.append acc (List.append allVarFromTerm1 allVarFromTerm2)
  | Eq (term1, term2) -> 
      let allVarFromTerm1 = getAllVarFromTerm term1 [] in
      let allVarFromTerm2 = getAllVarFromTerm term2 [] in
      List.append acc (List.append allVarFromTerm1 allVarFromTerm2)
  | PureAnd (pi1,pi2) -> 
      let temp1 = getAllVarFromPure pi1 [] in
      let temp2 = getAllVarFromPure pi2 [] in
      List.append acc (List.append temp1 temp2) 
  | Neg piN -> 
      List.append acc (getAllVarFromPure piN [])
  | PureOr (pi1,pi2) -> 
      let temp1 = getAllVarFromPure pi1 [] in
      let temp2 = getAllVarFromPure pi2 [] in
      List.append acc (List.append temp1 temp2) 
  | Predicate (_, termLi) -> List.fold_left termLi ~init:[] ~f:(fun acc t -> acc @ getAllVarFromTerm t [])

  ;;

let rec getAllNumFromPure (pi:pure):int list = 
  match pi with
  | Eq (term1, term2)
  | LtEq (term1, term2) 
  | GtEq (term1, term2)
  | Lt (term1, term2) 
  | Gt (term1, term2) -> 
    getAllNumFromTerm term1 @ getAllNumFromTerm term2
  | PureOr (pi1,pi2) 
  | PureAnd (pi1,pi2) -> 
    getAllNumFromPure pi1 @ getAllNumFromPure pi2
  | Neg piN -> getAllNumFromPure piN
  | Predicate (_, termLi) -> List.fold_left termLi ~init:[] ~f:(fun acc t -> acc @ getAllNumFromTerm t)
  | _ ->[]
  ;;


let rec getProgramValues (re:regularExpr) : int list = 
  match re with 
  | Emp | Bot -> [] 
  | Singleton (p, _) | Guard(p, _) -> getAllNumFromPure p 
  | Disjunction(r1, r2) 
  | Concate (r1, r2) -> getProgramValues r1 @ getProgramValues r2
  | Omega (reIn) | Kleene (reIn) -> getProgramValues reIn
  ;;


let addAssert (str:string) :string =
  "(assert " ^ str ^ " ) \n (check-sat) \n"
  ;;

let counter : int ref = ref 0 ;;


let (historyTable: ((string * bool)list)ref) = ref [] ;;

let rec existInhistoryTable pi table= 
  match table with 
  | [] -> None
  | (x, b)::xs -> 
    if String.compare x (string_of_pure pi) == 0 then Some b 
    else existInhistoryTable pi  xs




let rec term_to_expr ctx : terms -> Z3.Expr.expr = function
  | (Basic(BINT n))        -> Z3.Arithmetic.Real.mk_numeral_i ctx n
  | (Basic(BVAR v))           -> Z3.Arithmetic.Real.mk_const_s ctx v
  | (Basic(BNULL))           -> Z3.Arithmetic.Real.mk_const_s ctx "nil"
  | (Basic(BRET))           -> Z3.Arithmetic.Real.mk_const_s ctx "ret"
  | Basic (BSTR _)
  | Basic ANY -> raise (Failure "term_to_expr not yet")

  (*
  | Gen i          -> Z3.Arithmetic.Real.mk_const_s ctx ("t" ^ string_of_int i ^ "'")
  *)
  | Plus (t1, t2)  -> Z3.Arithmetic.mk_add ctx [ term_to_expr ctx t1; term_to_expr ctx t2 ]
  | Minus (t1, t2) -> Z3.Arithmetic.mk_sub ctx [ term_to_expr ctx t1; term_to_expr ctx t2 ]


let rec pi_to_expr ctx : pure -> Expr.expr = function
  | TRUE                -> Z3.Boolean.mk_true ctx
  | FALSE               -> Z3.Boolean.mk_false ctx
  | Gt (t1, t2) -> 
      let t1 = term_to_expr ctx t1 in
      let t2 = term_to_expr ctx t2 in
      Z3.Arithmetic.mk_gt ctx t1 t2
  | GtEq (t1, t2) -> 
      let t1 = term_to_expr ctx t1 in
      let t2 = term_to_expr ctx t2 in
      Z3.Arithmetic.mk_ge ctx t1 t2
  | Lt (t1, t2) -> 
      let t1 = term_to_expr ctx t1 in
      let t2 = term_to_expr ctx t2 in
      Z3.Arithmetic.mk_lt ctx t1 t2
  | LtEq (t1, t2) -> 
      let t1 = term_to_expr ctx t1 in
      let t2 = term_to_expr ctx t2 in
      Z3.Arithmetic.mk_le ctx t1 t2
  | Eq (t1, t2) -> 
      let newP = PureAnd (GtEq(t1, t2), LtEq(t1, t2)) in 
      pi_to_expr ctx newP
(*
  | Atomic (op, t1, t2) -> (
      let t1 = term_to_expr ctx t1 in
      let t2 = term_to_expr ctx t2 in
      match op with
      | Eq -> Z3.Boolean.mk_eq ctx t1 t2
      | Lt -> Z3.Arithmetic.mk_lt ctx t1 t2
      | Le -> Z3.Arithmetic.mk_le ctx t1 t2
      | Gt -> Z3.Arithmetic.mk_gt ctx t1 t2
      | Ge -> Z3.Arithmetic.mk_ge ctx t1 t2)
      *)
  | PureAnd (pi1, pi2)      -> Z3.Boolean.mk_and ctx [ pi_to_expr ctx pi1; pi_to_expr ctx pi2 ]
  | PureOr (pi1, pi2)       -> Z3.Boolean.mk_or ctx [ pi_to_expr ctx pi1; pi_to_expr ctx pi2 ]
  (*| Imply (pi1, pi2)    -> Z3.Boolean.mk_implies ctx (pi_to_expr ctx pi1) (pi_to_expr ctx pi2)
  *)
  | Neg pi              -> Z3.Boolean.mk_not ctx (pi_to_expr ctx pi)
  | Predicate (str, termLi) -> raise (Failure "to z3  expr not yet for predicate")



let check pi =
  let cfg = [ ("model", "false"); ("proof", "false") ] in
  let ctx = mk_context cfg in
  let expr = pi_to_expr ctx pi in
  (* print_endline (Expr.to_string expr); *)
  let goal = Goal.mk_goal ctx true true false in
  (* print_endline (Goal.to_string goal); *)
  Goal.add goal [ expr ];
  let solver = Solver.mk_simple_solver ctx in
  List.iter ~f:(fun a -> Solver.add solver [ a ]) (Goal.get_formulas goal);
  let sat = Solver.check solver [] == Solver.SATISFIABLE in
  (* print_endline (Solver.to_string solver); *)
  sat

let askZ3 pi = 
  match existInhistoryTable pi !historyTable with 
  | Some b  -> b
  | None ->
  
  let _ = counter := !counter + 1 in 
  let re = check pi in 
  let ()= historyTable := (string_of_pure pi, re)::!historyTable in 
  
  re;;


let entailConstrains pi1 pi2 = 

  let sat = not (askZ3 (Neg (PureOr (Neg pi1, pi2)))) in
  (*
  print_string (string_of_pure pi1 ^" -> " ^ string_of_pure pi2 ^" == ");
  print_string (string_of_bool (sat) ^ "\n");
  *)
  sat;;
  
(* 
let askZ3 pi = 
  let _ = counter := !counter + 1 in 
  (*
  let startTimeStamp = Sys.time() in
  *)
  
  let inFile = Sys.getcwd () ^ "/askZ3.txt" in
  let outFile = Sys.getcwd () ^ "/answerZ3.txt" in 
  let declear = List.fold_right (fun v acc ->acc ^ ("(declare-const " ^ v ^ " Int)\n") ) (checkRedundant (getAllVarFromPure pi [])) "" in
  let assertions = addAssert (convertPure (pi) "") in
  let oc = open_out inFile in    (* 新建或修改文件,返回通道 *)
      (*print_string (declear^assertions^"\n************\n");   (* 写一些东西 *)
      *)
      fprintf oc "%s\n" (declear^assertions);   (* 写一些东西 *)
      close_out oc;                (* 写入并关闭通道 *)
      ignore (Sys.command ("z3 -smt2 "^ inFile ^" > " ^ outFile));
      let ic = open_in outFile in
      try 
        let line = input_line ic in  (* 从输入通道读入一行并丢弃'\n'字符 *)
        close_in ic ;                 (* 关闭输入通道 *) 
        (*
        let verification_time = "[askZ3 Time: " ^ string_of_float (Sys.time() -. startTimeStamp) ^ " s]\n" in

        print_string (verification_time); 
        *)
        match line with 
        "sat" -> true
        | "unsat" -> false 
        | _ -> false 
      with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)
     
*)

(***********************************************)

let string_of_binary_tree tree = printTree ~line_prefix:"* " ~get_name ~get_children tree;; 

(***************************************)
(************   Datalog   **************)
(***************************************)


type basic_Type = Number | Symbol
type param  = string * basic_Type
type decl = string * (param list)

type relation = string * (terms list)
type head = relation
type body = Pos of relation | Neg of relation | Pure of pure 
type rule = head * (body list) 
type datalog = decl list * rule list

let compareRelation r1 r2 : bool = 
  let (s1, tL1) = r1 in 
  let (s2, tL2) = r2 in 
  if String.compare s1 s2 == 0 && compareTermList tL1 tL2 then true else false 

let compareBody b1 b2 : bool = 
  match (b1, b2) with 
  | (Pos r1, Pos r2) 
  | (Neg r1, Neg r2) -> compareRelation r1 r2 
  | (Pure p1, Pure p2) -> comparePure p1 p2 
  | _ -> false 

let rec compareBodyList (bodyL1:body list) (bodyL2:body list) : bool = 
  match bodyL1, bodyL2 with 
  | [], [] -> true 
  | (x:: xs, y:: ys) -> compareBody x y && compareBodyList xs ys 
  | _ -> false 


let rec expand_args (sep: string) (x:string list) = 
  match x with 
  [] -> ""
  | [x] -> x
  | x :: xs -> x ^ sep ^ (expand_args sep xs)



let sort_uniq cmp l =
  let rec rev_merge l1 l2 accu =
    match l1, l2 with
    | [], l2 -> List.rev_append l2 accu
    | l1, [] -> List.rev_append l1 accu
    | h1::t1, h2::t2 ->
        let c = cmp h1 h2 in
        if c == 0 then rev_merge t1 t2 (h1::accu)
        else if c < 0
        then rev_merge t1 l2 (h1::accu)
        else rev_merge l1 t2 (h2::accu)
  in
  let rec rev_merge_rev l1 l2 accu =
    match l1, l2 with
    | [], l2 -> List.rev_append l2 accu
    | l1, [] -> List.rev_append l1 accu
    | h1::t1, h2::t2 ->
        let c = cmp h1 h2 in
        if c == 0 then rev_merge_rev t1 t2 (h1::accu)
        else if c > 0
        then rev_merge_rev t1 l2 (h1::accu)
        else rev_merge_rev l1 t2 (h2::accu)
  in
  let rec sort n l =
    match n, l with
    | 2, x1 :: x2 :: tl ->
        let s =
          let c = cmp x1 x2 in
          if c == 0 then [x1] else if c < 0 then [x1; x2] else [x2; x1]
        in
        (s, tl)
    | 3, x1 :: x2 :: x3 :: tl ->
        let s =
          let c = cmp x1 x2 in
          if c == 0 then
            let c = cmp x2 x3 in
            if c == 0 then [x2] else if c < 0 then [x2; x3] else [x3; x2]
          else if c < 0 then
            let c = cmp x2 x3 in
            if c == 0 then [x1; x2]
            else if c < 0 then [x1; x2; x3]
            else
              let c = cmp x1 x3 in
              if c == 0 then [x1; x2]
              else if c < 0 then [x1; x3; x2]
              else [x3; x1; x2]
          else
            let c = cmp x1 x3 in
            if c == 0 then [x2; x1]
            else if c < 0 then [x2; x1; x3]
            else
              let c = cmp x2 x3 in
              if c == 0 then [x2; x1]
              else if c < 0 then [x2; x3; x1]
              else [x3; x2; x1]
        in
        (s, tl)
    | n, l ->
        let n1 = n asr 1 in
        let n2 = n - n1 in
        let s1, l2 = rev_sort n1 l in
        let s2, tl = rev_sort n2 l2 in
        (rev_merge_rev s1 s2 [], tl)
  and rev_sort n l =
    match n, l with
    | 2, x1 :: x2 :: tl ->
        let s =
          let c = cmp x1 x2 in
          if c == 0 then [x1] else if c > 0 then [x1; x2] else [x2; x1]
        in
        (s, tl)
    | 3, x1 :: x2 :: x3 :: tl ->
        let s =
          let c = cmp x1 x2 in
          if c == 0 then
            let c = cmp x2 x3 in
            if c == 0 then [x2] else if c > 0 then [x2; x3] else [x3; x2]
          else if c > 0 then
            let c = cmp x2 x3 in
            if c == 0 then [x1; x2]
            else if c > 0 then [x1; x2; x3]
            else
              let c = cmp x1 x3 in
              if c == 0 then [x1; x2]
              else if c > 0 then [x1; x3; x2]
              else [x3; x1; x2]
          else
            let c = cmp x1 x3 in
            if c == 0 then [x2; x1]
            else if c > 0 then [x2; x1; x3]
            else
              let c = cmp x2 x3 in
              if c == 0 then [x2; x1]
              else if c > 0 then [x2; x3; x1]
              else [x3; x2; x1]
        in
        (s, tl)
    | n, l ->
        let n1 = n asr 1 in
        let n2 = n - n1 in
        let s1, l2 = sort n1 l in
        let s2, tl = sort n2 l2 in
        (rev_merge s1 s2 [], tl)
  in
  let len = List.length l in
  if len < 2 then l else takefst (sort len l)


let string_of_param x =     
  match x with
  (n, Number) -> n ^ ":number"
| (s, Symbol) -> s ^ ":symbol" 

let string_of_relation (relation:relation) =
  match relation with
  (name,vars) -> let variables = expand_args "," (List.map vars ~f:string_of_terms) in name ^ "(" ^ variables ^ ")"  

  

let string_of_bodies (bodies:body list) = 
  expand_args ", " (List.map ~f:(fun body -> match body with
    Pos r -> string_of_relation r
  | Neg r -> "!"  ^ string_of_relation r
  | Pure p -> string_of_pure p 

  
  
  ) bodies)


let string_of_decl (decl:decl) =
  match decl with
  name,args -> ".decl "^ name ^ "(" ^ (expand_args "," (List.map ~f:string_of_param args ))  ^ ")"

let string_of_decls = List.fold_left ~f:(fun acc decl -> acc ^ (if acc != "" then "\n" else "") ^ string_of_decl decl ) ~init:""

let rec string_of_rules =  
  List.fold_left ~f:(fun acc (head,bodies) -> acc ^ (if acc != "" then "\n" else "") ^ string_of_relation head ^ " :- " ^ string_of_bodies bodies ^ "." ) ~init:""

let rec string_of_facts =  
  List.fold_left ~f:(fun acc (relation) -> acc ^ "\n" ^ string_of_relation relation ^ "." ) ~init:""

  


let param_compare (a:param) (b:param) =
  match (a,b) with
  (a_name,a_type), (b_name,b_type) -> 
    let nameDiff = String.compare a_name b_name in
    if nameDiff == 0 then (
      match (a_type, b_type) with
      (Number, Number)
      | (Symbol, Symbol) -> 0
      | (Number,Symbol) -> 1
      | (Symbol,Number) -> -1
    ) else nameDiff


let string_of_datalog (datalog:datalog) : string = 
  let (decls, rules) = datalog in 
  string_of_decls decls ^ string_of_rules rules

let rec infer_variables (pure:pure) =
  let get_variable_terms (x: terms) =
    match x with
    Basic (BVAR x) -> [Basic (BVAR x)]
    | _ -> [] in 
 let x = match pure with 
  TRUE -> []
  | FALSE -> []
  | Gt (a,b) -> (get_variable_terms a) @ (get_variable_terms b) 
  | Lt (a,b) ->  (get_variable_terms a) @ (get_variable_terms b)
  | GtEq (a,b) ->  (get_variable_terms a) @ (get_variable_terms b)
  | LtEq (a,b) ->  (get_variable_terms a) @ (get_variable_terms b)
  | Eq (a,b) -> (get_variable_terms a) @ (get_variable_terms b)
  | Neg (Eq(a,b)) -> (get_variable_terms a) @ (get_variable_terms b)
  | PureOr(a,b) -> (infer_variables a) @ (infer_variables b)
  | PureAnd(a,b) ->(infer_variables a) @ (infer_variables b)
  | Neg a -> infer_variables a
  | Predicate (s, termLi) -> flattenList (List.map ~f:get_variable_terms termLi)
  in sort_uniq (fun a b -> if stricTcompareTerm a b then 0 else 1) x
  (* | Pos a -> get_variable_terms a *)

let rec infer_params (pure:pure) : param list = 
  let get_variable_terms (x: terms) (y:basic_Type) =
    match x with
    Basic (BVAR x) -> [x,y]
    | _ -> [] in
  let x = match pure with 
  TRUE -> []
  | FALSE -> []
  | Gt (a,b) -> (get_variable_terms a Number) @ (get_variable_terms b Number) 
  | Lt (a,b) ->  (get_variable_terms a Number) @ (get_variable_terms b Number)
  | GtEq (a,b) ->  (get_variable_terms a Number) @ (get_variable_terms b Number)
  | LtEq (a,b) ->  (get_variable_terms a Number) @ (get_variable_terms b Number)
  (* TODO *)
  | Eq (a,b) -> (get_variable_terms a Number) @ (get_variable_terms b Number)
  | Neg (Eq(a,b)) -> (get_variable_terms a Number) @ (get_variable_terms b Number)
  | Neg a -> infer_params a
  | PureOr(a,b) -> (infer_params a) @ (infer_params b)
  | PureAnd(a,b) ->(infer_params a) @ (infer_params b)
  | Predicate (s, termLi) -> flattenList (List.map ~f:(fun a -> get_variable_terms a  Number) termLi)
  in sort_uniq param_compare x
  (*| Pos a -> get_variable_terms a *)



let rec translation (ctl:ctl) : string * datalog = 
  let fname, (decs,rules) = (translation_inner ctl) in
  let defaultDecs = [
    (entryKeyWord,     [ ("x", Number)]);  
    (valueKeyword,     [ ("x", Symbol); (locKeyWord, Number); ("n", Number)]);
    (assignKeyWord,    [ ("x", Symbol); (locKeyWord, Number); ("n", Number)]);
    (retKeyword,       [ ("n", Number); ("x", Number);]); (* currently only return integers *)
    (stateKeyWord,          [ ("x", Number)]);
    (flowKeyword,      [ ("x", Number); ("y", Number) ]);
    (transFlowKeyWord,      [ ("x", Number); ("y", Number) ]); 
    (leqKeyWord, [ ("x", Symbol); (locKeyWord, Number); ("n", Number)])
    ] in
  let defaultRules = [ 
    (transFlowKeyWord, [Basic (BVAR "x"); Basic (BVAR "y")] ), [ Pos (flowKeyword, [Basic (BVAR "x"); Basic (BVAR "y")]) ] ;
    (transFlowKeyWord, [Basic (BVAR "x"); Basic (BVAR "z")] ), [ Pos (flowKeyword, [Basic (BVAR "x"); Basic (BVAR "y")]); Pos (transFlowKeyWord, [Basic (BVAR "y"); Basic (BVAR "z")]) ];
    
    (valueKeyword, [Basic (BVAR "x"); Basic (BVAR locKeyWord); Basic (BVAR "n")] ), [ Pos (assignKeyWord, [Basic (BVAR "x"); Basic (BVAR locKeyWord); Basic (BVAR "n")]) ] ;
    (valueKeyword, [Basic (BVAR "x"); Basic (BVAR locKeyWord); Basic (BVAR "n")] ), 
      [ Pos (valueKeyword, [Basic (BVAR "x"); Basic (BVAR loc_inter_KeyWord); Basic (BVAR "n")] );  
        Pos (flowKeyword, [Basic (BVAR loc_inter_KeyWord); Basic (BVAR locKeyWord)]); 
        Neg (assignKeyWord, [Basic (BVAR "x"); Basic (BVAR locKeyWord); Basic ANY]) ] ;
    ] in

    
    (**********************************************************************
    The following code is to add the top level rule to only show the 
    reslts on the entry pointes. For example, if the query is: 
    EF_terminating(loc); then it will be added with the following EF_terminatingFinal rule 
    EF_terminatingFinal(loc) :- entry(loc), EF_terminating(loc).     
    --- Yahui Song
    **********************************************************************)
    let decs, rules  = 
    (match rules with 
    | ((name, [Basic (BVAR locKeyWord)]), _)::_ -> 
      let nameFinal = name^outputShellKeyWord in 
      let finaDecl = (nameFinal,     [ (locKeyWord, Number)]) in 
      let finalRule = ((nameFinal, [Basic (BVAR locKeyWord)]), [Pos(entryKeyWord,  [Basic (BVAR locKeyWord)]) ; Pos (name, [Basic (BVAR locKeyWord)])]) in 
      finaDecl::decs,  finalRule::rules
    | _ -> decs, rules
    ) in 

    fname, (defaultDecs @ List.rev decs, defaultRules @ List.rev rules)

  
and get_params (declarations: decl list) =
    match declarations with
    [] -> []
    | x :: xs -> snd x


and get_args (rules: rule list) =
    match rules with
    | [] -> []
    | x::xs -> snd (takefst x) 

and process_args (args:terms list) =
    sort_uniq 
    (fun x y -> 
      match (x,y) with
      | (Basic (BVAR x), Basic (BVAR y)) -> String.compare x y
      | _ -> raise (Failure "Arguments should only be variables")
      )
    (List.filter ~f:(fun x -> match x with  Basic (BVAR x) -> true | _ -> false ) args ) 


and translation_inner (ctl:ctl) : string * datalog =

    let processPair f1 f2 name (construct_rules: relation -> relation -> relation -> rule list) =
      let x1,(f1Declarations,f1Rules) = translation_inner f1 in
      let x2,(f2Declarations,f2Rules) = translation_inner f2 in
      let f1Params = get_params f1Declarations in
      let f2Params = get_params f2Declarations in
      let f1Args = get_args f1Rules in
      let f2Args = get_args f2Rules in
      let decs = List.append f1Declarations f2Declarations in
      let ruls = List.append f1Rules f2Rules in
      let newParams = (sort_uniq param_compare (List.append f1Params f2Params)) in
      let newArgs = process_args (List.append f1Args f2Args) in
      let newName = name x1 x2 in 
      newName, ( (newName,newParams) :: decs, ( (construct_rules (newName, newArgs) (x1,f1Args) (x2,f2Args))  @ ruls)) 
    in

    match ctl with 
    | Atom (pName, pure) -> 
      let vars = Basic (BVAR locKeyWord) :: infer_variables pure in
      let params =  (locKeyWord , Number) :: infer_params pure in
      let valuationAtom var = Pos (valueKeyword, [Basic (BSTR var); Basic (BVAR locKeyWord); Basic(BVAR (var^"_v"))] ) in 
      (match pure with 
      | Gt(Basic (BSTR x), Basic (BINT n) ) -> 
        pName,([(pName,params)], [  ((pName, vars), [Pos(stateKeyWord, [Basic (BVAR locKeyWord)]) ; valuationAtom x; Pure (Gt(Basic(BVAR (x^"_v")), Basic (BINT n) ))]) ])
      | GtEq(Basic (BSTR x), Basic (BINT n) ) -> 
        pName,([(pName,params)], [  ((pName, vars), [Pos(stateKeyWord, [Basic (BVAR locKeyWord)]) ; valuationAtom x; Pure (GtEq(Basic(BVAR (x^"_v")), Basic (BINT n) ))]) ])

      | Lt(Basic (BSTR x), Basic (BINT n) ) -> 
        pName,([(pName,params)], [  ((pName, vars), [Pos(stateKeyWord, [Basic (BVAR locKeyWord)]) ; valuationAtom x; Pure (Lt(Basic(BVAR (x^"_v")), Basic (BINT n) ))]) ])

      | Eq(Basic (BSTR x), Basic (BINT n) ) -> 
        pName,([(pName,params)], [  ((pName, vars), [Pos(stateKeyWord, [Basic (BVAR locKeyWord)]) ; valuationAtom x; Pure (Eq(Basic(BVAR (x^"_v")), Basic (BINT n) ))]) ])

      | Neg(Eq(Basic (BSTR x), Basic (BINT n) )) -> 
        pName,([(pName,params)], [  ((pName, vars), [Pos(stateKeyWord, [Basic (BVAR locKeyWord)]) ; valuationAtom x; Pure (Neg (Eq(Basic(BVAR (x^"_v")), Basic (BINT n) )))]) ])


      (* *********************************************************************
      The above the pattern matching is needed for checking variables' values, for example, 
      "x" > 1 will be written as valuation("x", loc, x_v), x_v>1. 
      --- Yahui Song
      ********************************************************************* *)
      | _ ->  pName,([(pName,params)], [  ((pName, vars), [Pos(stateKeyWord, [Basic (BVAR locKeyWord)]) ; Pure pure]) ])
      )
    
    | Neg f -> 
      let fName,(declarations,rules) = translation_inner f in
        let newName = "NOT_" ^ fName in
        let fParams = get_params declarations in
        let fArgs = get_args rules in
        newName,(  (newName,fParams) :: declarations, ( (newName,fArgs), [Pos(stateKeyWord, [Basic (BVAR locKeyWord)]) ;Neg (fName,fArgs) ]):: rules)

    | Conj (f1 , f2) -> 
        processPair f1 f2 
        (fun x1 x2 ->  x1 ^ "_AND_" ^ x2) 
        (fun (newName,newArgs) (x1,f1Args) (x2,f2Args) -> [( (newName, newArgs) , [Pos(x1,f1Args); Pos(x2,f2Args)] ) ])
      
    | Disj (f1,f2) ->
        processPair f1 f2 
        (fun x1 x2 ->  x1 ^ "_OR_" ^ x2) 
        (fun (newName,newArgs) (x1,f1Args) (x2,f2Args) -> [ ( (newName, newArgs) , [Pos(x1,f1Args)] ) ; ( (newName, newArgs) , [Pos(x2,f2Args)] ) ]);
      
    | Imply (f1,f2) -> 
        processPair f1 f2 
        (fun x1 x2 ->  x1 ^ "_IMPLY_" ^ x2) 
        (fun (newName,newArgs) (x1,f1Args) (x2,f2Args) -> 
        [ ( (newName, newArgs) , [Pos(x2,f2Args)]);
          ( (newName, newArgs) , [Pos(stateKeyWord, [Basic (BVAR locKeyWord)]) ; Neg(x1,f1Args)] )
        ])

    (* Primary CTL Encoding *)
    (* The idea behind this encoding is state encoding is to reuse the previous name when a transition is needed *)
    | EX f ->   
      (* TODO *)  
      let fName,(declarations,rules) = translation_inner f in
        let newName = "EX_" ^ fName in
        let fParams = get_params declarations in
        let fArgs = get_args rules in
        let arg = Basic (BVAR "tempOne") in
        let firstArg, fNewArgs = match fArgs with
          [] -> raise (Failure "confused")
          | x :: xs -> x, arg :: xs in
        newName,(  (newName,fParams) :: declarations, ( (newName,fArgs), [  Pos(flowKeyword, [firstArg;arg] );    Pos (fName,fNewArgs) ]):: rules)
    | EF f ->     
      let fName,(declarations,rules) = translation_inner f in
      (* TODO *)
        let newName = "EF_" ^ fName in
        let fParams = get_params declarations in
        let fArgs = get_args rules in
        let arg = Basic (BVAR "tempOne") in
        let firstArg, fNewArgs = match fArgs with
          [] -> raise (Failure "confused") 
          | x :: xs -> x, arg :: xs in
        newName,(  (newName,fParams) :: declarations, 
        [
          ( (newName,fArgs), [Pos (fName,fArgs) ]);
          ( (newName,fArgs), [Pos(flowKeyword,[firstArg;arg]); Pos(newName,fNewArgs)     ] )

        ]@ rules) 
    
    | AF f ->     
      (* Per Gottlob et al.

      AF_P_T(x,z) :- AF_P_T(x,y), !P(y), flow(y,z);
      AF_P_T(x,y) :- !P(x), flow(x,y);
      AF_P_S(x) :- AF_P_T(x,x);
      AF_P_S(x) :- !P(x), flow(x,y), S(y);
      AF_P(x) :- state(x) !AF_P_S(x);

      The approach here makes y and z first to allow for easier manipulation 

      *)
      let fName,(declarations,rules) = 
        match f with 

        | Atom (notPName, Lt(Basic (BSTR x), Basic (BINT n))) -> 

          let negetionName, (negetionDecl, negetionRules) = translation_inner (Atom ("not_"^notPName,  GtEq(Basic (BSTR x), Basic (BINT n)))) in 
          
          let findallDecl = (notPName, [ (locKeyWord, Number)]) in  
          let findallRules = (notPName, [Basic (BVAR locKeyWord)] ), [ Pos (stateKeyWord, [Basic (BVAR locKeyWord)]); Pos(valueKeyword, [Basic (BSTR x); Basic (BVAR locKeyWord); Basic(ANY)]); Neg(negetionName, [Basic (BVAR locKeyWord)]) ] in  


          notPName, (findallDecl :: negetionDecl, findallRules :: negetionRules)

        | Atom (notPName, Eq(Basic (BSTR x), Basic (BINT n))) -> 

          let negetionName, (negetionDecl, negetionRules) = translation_inner (Atom ("not_"^notPName,  Neg (Eq(Basic (BSTR x), Basic (BINT n))))) in 
          
          let findallDecl = (notPName, [ (locKeyWord, Number)]) in  
          let findallRules = (notPName, [Basic (BVAR locKeyWord)] ), [ Pos (stateKeyWord, [Basic (BVAR locKeyWord)]); Pos(valueKeyword, [Basic (BSTR x); Basic (BVAR locKeyWord); Basic(ANY)]); Neg(negetionName, [Basic (BVAR locKeyWord)]) ] in  


          notPName, (findallDecl :: negetionDecl, findallRules :: negetionRules)


      (* *********************************************************************
      The above the pattern matching is needed for constructing the atomic P rules, 
      when we are computing AF p. Usually the encoding needs simple "!P". 
      But since the analysis may be overapproximating, we need to compute “for sure !P” 
      For example, AF x<0, will be encoded as: 

      1) not_xIsSmallerThan_0(loc) :- state(loc), valuation("x",loc,x_v), (x_v >= 0).
      2) xIsSmallerThan_0(loc) :- state(loc), valuation("x",loc,_), !not_xIsSmallerThan_0(loc).

      where 1) captures the negation of x<0, then 2) captures "for sure x<0", 
      then subsequently, we can use !xIsSmallerThan_0 as usual. 

      --- Yahui Song
      ********************************************************************* *)

        | _ -> translation_inner f in
      let newName = "AF_" ^ fName in
      let sName = newName ^ "_S" in
      let tName = newName ^ "_T" in
      let fParams = get_params declarations in
      let fArgs = get_args rules in
      let arg = Basic (BVAR "tempOne") in
      let firstArg, fNewArgs, fArgsTail = 
        match fArgs with
        [] ->  raise (Failure "confused")
        | x :: xs -> x, arg :: xs, xs in

      let tArg = Basic (BVAR "interm_state") in
      let tParam = "interm_state" , Number in
      let tArgs = tArg :: fArgs in
      let tNewArgs = arg :: fArgs in
      let tParams = tParam :: fParams in

      let newDeclarations = [
        (newName,fParams);
        (sName,fParams);
        (tName, tParams);

      ] in
      let newRules = [
        (newName,fArgs), [Pos(stateKeyWord, [firstArg]); Neg (sName, fArgs)];

        (sName, fArgs), [Pos(tName, firstArg :: firstArg :: fArgsTail)];
        (* for finite traces *)
        (* (sName,fArgs), [ Neg(fName, fArgs); Pos("end", [firstArg])];  *)
        (* for infinite traces *)
        (sName,fArgs), [ Neg(fName, fArgs); Pos(flowKeyword, [firstArg; arg]); Pos(sName,fNewArgs)  ];

        (tName, tArgs), [ Neg(fName,fArgs); Pos(flowKeyword, [firstArg; tArg] ) ];
        (tName, tArgs), [ Pos(tName,tNewArgs) ;Neg(fName,fNewArgs); Pos(flowKeyword, [arg; tArg] ) ];
        

      ] in
      newName,( newDeclarations @ declarations, newRules @ rules)
 
    
    | EU (f1,f2)->
      processPair f1 f2 
      (fun x1 x2 ->  x1 ^ "_EU_" ^ x2) 
      (fun (newName,newArgs) (x1,f1Args) (x2,f2Args) -> 
        let arg = Basic (BVAR "tempOne") in
        let firstArg, fNewArgs = match newArgs with
        [] -> raise (Failure "confused")
        | x :: xs -> x, arg :: xs in
        [ 
        (newName,newArgs) , [ Pos(x2,f2Args) ];
        (newName,newArgs) , [ Pos(x1,f1Args); Pos(flowKeyword,[arg;firstArg]); Pos(newName,fNewArgs) ];
      ])

    
      
    (* Derivative rules *)
    | AX f ->
      (* AX f = !EX !f *)     
      let fName,(declarations,rules) = translation_inner  (EX (Neg f)) in
      let prefixLen = (List.fold_right ~f:(+) (List.map ~f:String.length [ "EX_"; "NOT_"]) ~init:0) in
      let newName = "AX_" ^  (String.sub fName prefixLen (String.length fName - prefixLen)) in
      let fParams = get_params declarations in
      let fArgs = get_args rules in
        newName,(  (newName,fParams) :: declarations, ( (newName,fArgs), [Pos(stateKeyWord, [ Basic (BVAR locKeyWord)]);Neg (fName,fArgs) ]):: rules)
    
    | AG f ->
      (* AG f  = !EF !f *)     
      let fName,(declarations,rules) = translation_inner (EF (Neg f)) in
      let prefixLen = (List.fold_right ~f:(+) (List.map ~f:String.length [ "EF_"; "NOT_"]) ~init:0) in
      let newName = "AG_" ^  (String.sub fName prefixLen (String.length fName - prefixLen)) in
      let fParams = get_params declarations in
      let fArgs = get_args rules in
        newName,(  (newName,fParams) :: declarations, ( (newName,fArgs), [Pos(stateKeyWord, [ Basic (BVAR locKeyWord)]) ;Neg (fName,fArgs) ]):: rules)

    | EG f ->
      (* EG f = !AF !f *)     
      let fName,(declarations,rules) = translation_inner (AF (Neg f)) in
      let prefixLen = (List.fold_right ~f:(+) (List.map ~f:String.length [ "AF_"; "NOT_"]) ~init:0) in
      let newName = "EG_" ^  (String.sub fName prefixLen (String.length fName - prefixLen)) in
      let fParams = get_params declarations in
      let fArgs = get_args rules in
        newName,(  (newName,fParams) :: declarations, ( (newName,fArgs), [Pos(stateKeyWord, [ Basic (BVAR locKeyWord)]) ;Neg (fName,fArgs) ]):: rules)

    | AU (f1,f2) ->
      (* f1 AU f2 = not (!f2 EU (!f1 and !f2) ) and AF f2 *)
      let x1,_ = translation_inner f1 in
      let x2,_ = translation_inner f2 in
      let eu = EU((Neg f2),(Conj((Neg f1),(Neg f2)))) in
      let fName,(declarations,rules) = translation_inner (Conj((AF f2),(Neg eu))) in
      let newName = x1 ^ "_AU_" ^ x2 in
      let fParams = get_params declarations in
      let fArgs = get_args rules in
        newName,(  (newName,fParams) :: declarations, ( (newName,fArgs), [Pos (fName,fArgs) ]):: rules)

    
  (* core, EX, AF, AU, the rest needs to be translated *)
