open Z3

type basic_type = BINT of int | BVAR of string | BNULL | BRET | ANY

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
  | Emp of state 
  | Singleton of (pure * state)
  | Disjunction of (regularExpr * regularExpr)
  | Concate of (regularExpr * regularExpr)
  | Kleene of regularExpr
  | Omega of regularExpr 
  | Guard of (pure * state)

type ctl = 
    Atom of pure 
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
  | ANY -> "*"

let string_of_basic_t_aux v = 
  match v with 
  | BVAR name -> "\""^name ^"\""
  | BINT n -> string_of_int n
  | BNULL -> "NULL"
  | BRET -> "\"" ^"ret"^ "\""
  | ANY -> "*"


let basic_type2_string v = 
  match v with 
  | BVAR name -> [name]
  | BINT _ 
  | BNULL 
  | BRET -> []

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
  | GtEq (t1, t2) -> (string_of_terms t1) ^ "≥" ^ (string_of_terms t2)
  | LtEq (t1, t2) -> (string_of_terms t1) ^ "≤" ^ (string_of_terms t2)
  | Eq (t1, t2) -> (string_of_terms t1) ^ "=" ^ (string_of_terms t2)
  | PureOr (p1, p2) -> "("^string_of_pure p1 ^ "∨" ^ string_of_pure p2^")"
  | PureAnd (p1, p2) -> string_of_pure p1 ^ "∧" ^ string_of_pure p2
  | Neg (Eq (t1, t2)) -> "("^(string_of_terms t1) ^ "!=" ^ (string_of_terms t2)^")"
  | Neg p -> "!(" ^ string_of_pure p^")"
  | Predicate (str, termLi) -> str ^ "(" ^ string_of_list_terms termLi ^ ")"


let rec string_of_ctl (ctl:ctl) = 
  match ctl with
  | Atom p -> string_of_pure p 
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
  | Emp (state)       -> "𝝐 " ^ string_of_loc state
  | Singleton (p, state)  -> "(" ^string_of_pure p  ^ ")"^ string_of_loc state
  | Concate (eff1, eff2) -> string_of_regularExpr eff1 ^ " · " ^ string_of_regularExpr eff2 
  | Disjunction (eff1, eff2) ->
      "((" ^ string_of_regularExpr eff1 ^ ") \\/ (" ^ string_of_regularExpr eff2 ^ "))"
  | Kleene effIn          ->
      "(" ^ string_of_regularExpr effIn ^ ")^*"
     
  | Omega effIn          ->
      "(" ^ string_of_regularExpr effIn ^ ")^w"

  | Guard (p, state) -> "[" ^ string_of_pure p^ "]" ^ string_of_loc state (*^ string_of_regularExpr effIn*)




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



let string_of_event (str, li) = 
  let temp = 
    match li with 
    | [] -> ""
    | [x] ->  string_of_basic_t x 
    | x::xs->
      List.fold_left xs 
      ~init:(string_of_basic_t x) 
      ~f:(fun acc a -> acc ^ "," ^ string_of_basic_t a )
  in 
  str ^ "("^temp^")"



let rec string_of_bt_list (li: basic_type list) : string = 
    match li with 
  | [] -> ""
  | [x] -> string_of_basic_t_aux x 
  | x::xs -> string_of_basic_t_aux x ^ ", " ^ string_of_bt_list xs


let string_of_fact (str, btList) = 
  str ^ "(" ^ 
  string_of_bt_list btList 
  (* List.fold_left btList ~init:"" ~f:(fun acc a -> acc ^ string_of_basic_t a) *)
  ^ ")"


let rec string_of_facts (factsLi) = 
  match factsLi with 
  | [] -> ""
  | [fact] -> string_of_fact fact ^ "."
  | fact :: xs -> string_of_fact fact ^ ".\n" ^ string_of_facts xs 
  

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

