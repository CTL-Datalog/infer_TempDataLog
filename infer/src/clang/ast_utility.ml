open Z3

type basic_type = BINT of int | BVAR of string | BNULL | BRET


type event = string * (basic_type list)


type ltl = Lable of event 
        | Next of ltl
        | Until of ltl * ltl
        | Global of ltl
        | Future of ltl
        | NotLTL of ltl
        | Imply of ltl * ltl
        | AndLTL of ltl * ltl
        | OrLTL of ltl * ltl

type line_number = int option

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



type mnsigniture = (string *  (string list))
type fact = (string *  (basic_type list)) 

type specification = (mnsigniture * fact list)


(* Global States *)
let (varSet: (string list) ref) = ref [] 
let (handlerVar: string option ref) = ref None 

(* Experimental Summary *)
let totol_execution_time  = ref 0.0
let totol_Lines_of_Code  = ref 0
let totol_Lines_of_Spec  = ref 0

let currentFunctionLineNumber = ref (0, 0) 


let (totol_specifications: (specification list) ref)  = ref []


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

let basic_type2_string v = 
  match v with 
  | BVAR name -> [name]
  | BINT _ 
  | BNULL 
  | BRET -> []



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
  | [x] -> string_of_basic_t x 
  | x::xs -> string_of_basic_t x ^ ", " ^ string_of_bt_list xs


let string_of_fact (str, btList) = 
  str ^ "(" ^ 
  string_of_bt_list btList 
  (* List.fold_left btList ~init:"" ~f:(fun acc a -> acc ^ string_of_basic_t a) *)
  ^ ")"


let rec string_of_facts (factsLi) = 
  match factsLi with 
  | [] -> ""
  | [fact] -> string_of_fact fact
  | fact :: xs -> string_of_fact fact ^ "\n" ^ string_of_facts xs 
  

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
  | (Basic (BNULL)) -> " " ^ "nil" ^ " "
  | Plus (t1, t2) -> ("(+") ^ (convertTerm t1) ^  (convertTerm t2) ^ ")"
  | Minus (t1, t2) -> ("(-") ^ (convertTerm t1) ^  (convertTerm t2) ^ ")"
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


module Color = struct
  (* use ANSI color codes, see https://en.wikipedia.org/wiki/ANSI_escape_code *)
  type color =
    | Black
    | Red
    | Green
    | Yellow
    | Blue
    | Magenta
    | Cyan
    | White
  ;;

  type style =
    | FG of color (* foreground *)
    | BG of color (* background *)
    | Bold
    | Reset

  let ansi_of_color = function
    | Black -> "0"
    | Red -> "1"
    | Green -> "2"
    | Yellow -> "3"
    | Blue -> "4"
    | Magenta -> "5"
    | Cyan -> "6"
    | White -> "7"

  let code_of_style = function
    | FG c -> "3" ^ ansi_of_color c
    | BG c -> "4" ^ ansi_of_color c
    | Bold -> "1"
    | Reset -> "0"

  let ansi_of_style_l l =
    let s = match l with
      | [] -> code_of_style Reset
      | [s] -> code_of_style s
      | _ -> String.concat ~sep:";" (List.map ~f:code_of_style l)
    in
    "\x1b[" ^ s ^ "m"

  type styles = {
    error: style list;
    warning: style list;
    loc: style list;
  }

  let default_styles = {
    warning = [Bold; FG Magenta];
    error = [Bold; FG Red];
    loc = [Bold];
  }

  let cur_styles = ref default_styles
  let get_styles () = !cur_styles
  let set_styles s = cur_styles := s

  (* map a tag to a style, if the tag is known.
     @raise Not_found otherwise *)
  let style_of_tag s = match s with
    | Format.String_tag "error" -> (!cur_styles).error
    | Format.String_tag "warning" -> (!cur_styles).warning
    | Format.String_tag "loc" -> (!cur_styles).loc
    | _ -> raise Not_found

  let color_enabled = ref true

  (* either prints the tag of [s] or delegates to [or_else] *)
  let mark_open_tag ~or_else s =
    try
      let style = style_of_tag s in
      if !color_enabled then ansi_of_style_l style else ""
    with Not_found -> or_else s

  let mark_close_tag ~or_else s =
    try
      let _ = style_of_tag s in
      if !color_enabled then ansi_of_style_l [Reset] else ""
    with Not_found -> or_else s

  (* add color handling to formatter [ppf] *)
  let set_color_tag_handling (ppf:Format.formatter) =
    let open Format in
    let functions = pp_get_formatter_stag_functions ppf () in
    let functions' = {functions with
      mark_open_stag=(mark_open_tag ~or_else:functions.mark_open_stag);
      mark_close_stag=(mark_close_tag ~or_else:functions.mark_close_stag);
    } in
    pp_set_mark_tags ppf true; (* enable tags *)
    pp_set_formatter_stag_functions ppf functions';
    ()

  external isatty : out_channel -> bool = "caml_sys_isatty"

  (* reasonable heuristic on whether colors should be enabled *)
  let should_enable_color () =
    let (term:string) = 
      try 
        (match Sys.getenv "TERM" with
        | Some str -> str 
        | None -> "")
      with Not_found -> "" in
    (String.compare term "dumb" != 0)
    && (String.compare term "" != 0 )
    && isatty stderr

  type setting = Auto | Always | Never

  let default_setting = Auto

  let setup =
    let first = ref true in (* initialize only once *)
    let (formatter_l: Format.formatter list) =
      [Format.std_formatter; Format.err_formatter; Format.str_formatter]
    in
    let enable_color = function
      | Auto -> should_enable_color ()
      | Always -> true
      | Never -> false
    in
    fun o ->
      if !first then (
        first := false;
        Format.set_mark_tags true;
        List.iter ~f:set_color_tag_handling formatter_l;
        color_enabled := (match o with
          | Some s -> enable_color s
          | None -> enable_color default_setting)
      );
      ()
end

let colours : [`Html|`Ansi|`None] ref = ref `None

let col ~ansi ~html text = 
  (match !colours with
  | `None -> ""
  | `Ansi -> ansi
  | `Html -> html) ^ text ^
  (match !colours with
  | `None -> ""
  | `Ansi -> "\u{001b}[0m"
  | `Html -> "</span>")
 
let red text = col ~ansi:"\u{001b}[31m" ~html:"<span class=\"output-error\">" text
let green text = col ~ansi:"\u{001b}[32m" ~html:"<span class=\"output-ok\">" text
let yellow text = col ~ansi:"\u{001b}[33m" ~html:"<span class=\"output-emph\">" text
let emph text = col ~ansi:"\u{001b}[1;4m" ~html:"<span class=\"output-emph\">" text


let debug_print title s =
  print_endline (yellow title);
  print_endline s;
  if not (String.equal "" s) then print_endline ""

let info ~title fmt =
  Format.kasprintf
    (fun s -> debug_print title s)
    fmt
