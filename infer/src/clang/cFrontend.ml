(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open Unix
open Ast_utility
open Parser
open Lexer
module L = Logging
module F = Format


(* ocamlc gets confused by [module rec]: https://caml.inria.fr/mantis/view.php?id=6714 *)
(* it also ignores the warning suppression at toplevel, hence the [include struct ... end] trick *)
include struct
  [@@@warning "-60"]

  module rec CTransImpl : CModule_type.CTranslation = CTrans.CTrans_funct (CFrontend_declImpl)
  and CFrontend_declImpl : CModule_type.CFrontend = CFrontend_decl.CFrontend_decl_funct (CTransImpl)
end

(* Translates a file by translating the ast into a cfg. *)
let compute_icfg trans_unit_ctx tenv ast =
  match ast with
  | Clang_ast_t.TranslationUnitDecl (_, decl_list, _, _) ->
      CFrontend_config.global_translation_unit_decls := decl_list ;
      L.(debug Capture Verbose) "@\n Start creating icfg@\n" ;
      let cfg = Cfg.create () in
      List.iter
        ~f:(CFrontend_declImpl.translate_one_declaration trans_unit_ctx tenv cfg `DeclTraversal)
        decl_list ;
      L.(debug Capture Verbose) "@\n Finished creating icfg@\n" ;
      cfg
  | _ ->
      assert false


(* NOTE: Assumes that an AST always starts with a TranslationUnitDecl *)

let init_global_state_capture () =
  Ident.NameGenerator.reset () ;
  CFrontend_config.global_translation_unit_decls := [] ;
  CFrontend_config.reset_block_counter ()

module IDM = Map.Make(String)

let node_map = ref IDM.empty
let node_val = ref 0

let string_of_source_range ((s1, s2):Clang_ast_t.source_range) :string = 
  match (s1.sl_file, s2.sl_file) with 
  | (Some name, _) 
  | (_, Some name) -> name
  | (_, _) -> "none"






let rec decomposePure p : pure list = 
  match p with 
  | PureOr (p1, p2)
  | PureAnd (p1, p2) -> decomposePure p2 @ decomposePure p1
  | Ast_utility.TRUE -> []
  | _ -> [p]



let conjunctPure (pi1:pure) (pi2:pure): pure = 
  if entailConstrains pi1 pi2 then pi1 
  else if entailConstrains pi2 pi1 then pi2
  else  
    let pi1 = normalise_pure pi1 in 
    let pi2 = normalise_pure pi2 in 
    (match pi1, pi2 with 
    | ((GtEq(Basic (BSTR var1), Basic(BINT 0))), PureAnd (pi11, LtEq(Basic (BSTR var2), Basic(BINT 0)))) -> 
      if String.compare var1 var2 == 0 then PureAnd(Eq(Basic (BSTR var1), Basic(BINT 0)), pi11)
      else PureAnd (pi1, pi2)
    | ((GtEq(Basic (BSTR var1), Basic(BINT 0))), LtEq(Basic (BSTR var2), Basic(BINT 0))) -> 
      if String.compare var1 var2 == 0 then Eq(Basic (BSTR var1), Basic(BINT 0))
      else PureAnd (pi1, pi2)

    | _, _ -> PureAnd (pi1, pi2)
    )
    (*
    let pLi = decomposePure (PureAnd (pi1, pi2)) in 
    let rec sortList (acc:(string * (pure list)) list) li = 
      match li with 
      | [] -> acc 
      | px :: xs-> 
        (match px with 
        | Eq (Basic (BSTR var), t2) -> 

          (match findFromRecord acc var with 
          | None -> 
            let acc' = (var, [px]): acc'  in 
            sortList acc' xs 
          | Some (acc', pureLi) -> 
            let acc2 = (var, px::pureLi): acc'  in 
            sortList acc2 xs )
        | _ -> 
            
        )

    in 
    let sortsByVar = sortList [] pLi in 
    let rec iterateSort (acc:(string * (pure list)) list) : (pure list) =    
    *)

    

  
  



let rec findReturnValue (pi:pure) : terms option = 
  match pi with
  | Eq (Basic (BRET), t2) 
  | Eq (t2, Basic (BRET)) -> Some t2 
  | Predicate _
  | TRUE 
  | FALSE 
  | Gt _ 
  | Lt _ 
  | GtEq _ 
  | LtEq _ 
  | Neg _ 
  | Eq _ -> None 
  | PureAnd (pi1, pi2) 
  | PureOr (pi1,pi2) -> 
      (match findReturnValue pi1 with 
      | None -> findReturnValue pi2 
      | Some t -> Some t)
  




  
let stmt2Pure_helper (op: string) (t1: terms option) (t2: terms option) : pure option = 
  match (t1, t2) with 
  | (None, _) 
  | (_, None ) -> None 
  | (Some t1, Some t2) -> 
    let p = 
      if String.compare op "<" == 0 then Lt (t1, t2)
    else if String.compare op ">" == 0 then Gt (t1, t2)
    else if String.compare op ">=" == 0 then GtEq (t1, t2)
    else if String.compare op "<=" == 0 then LtEq (t1, t2)
    else if String.compare op "!=" == 0 then Neg (Eq (t1, t2))

    else Eq (t1, t2)
    in Some p 




let getStmtlocation (instr: Clang_ast_t.stmt) : (int option * int option) =
  match instr with 
  | CompoundStmt (stmt_info, _) 
  | DeclStmt (stmt_info, _, _) 
  | ReturnStmt (stmt_info, _) 
  | UnaryOperator (stmt_info, _, _, _) 
  | ImplicitCastExpr (stmt_info, _, _, _, _) 
  | BinaryOperator (stmt_info, _, _, _)
  | CompoundAssignOperator (stmt_info, _, _, _, _)
  | CallExpr (stmt_info, _, _)  
  | ParenExpr (stmt_info (*{Clang_ast_t.si_source_range} *), _, _)
  | ArraySubscriptExpr (stmt_info, _, _) 
  | UnaryExprOrTypeTraitExpr (stmt_info, _, _, _)
  | IfStmt (stmt_info, _, _) 
  | CXXConstructExpr (stmt_info, _, _, _)
  | ExprWithCleanups (stmt_info, _, _, _)
  | CXXDeleteExpr (stmt_info, _, _, _)
  | ForStmt (stmt_info, _)
  | SwitchStmt (stmt_info, _, _)
  | CXXOperatorCallExpr (stmt_info, _, _)
  | CStyleCastExpr (stmt_info, _, _, _, _)  ->
    let (sl1, sl2) = stmt_info.si_source_range in 
    (sl1.sl_line , sl2.sl_line)

  | _ -> (None, None) 

let maybeIntToListInt ((s1, s2):(int option * int option )) : (int list * int list)  = 
  let aux l = match l with | None -> [] | Some l -> [l] 
  in (aux s1, aux s2)


let stmt_intfor2FootPrint (stmt_info:Clang_ast_t.stmt_info): (int list * int list) = 
  let ((sl1, sl2)) = stmt_info.si_source_range in 
    (* let (lineLoc:int option) = sl1.sl_line in *)
  maybeIntToListInt (sl1.sl_line, sl2.sl_line) 


let rec findCallSpecFrom (specs:specification list) (fName: string): (mnsigniture * fact list) option = 
  match specs with 
  | [] -> None
  | (CallStmt (str, li), facts):: rest -> 
    if String.compare str fName == 0 then Some ((str, li), facts) else 
    findCallSpecFrom rest fName
  | _ :: rest -> findCallSpecFrom rest fName    
  ;;

let rec findIfStmtSpecFrom (specs:specification list) (piCondition: pure): (bindings * fact list) option = 
  match specs with 
  | [] -> None
  | (IfStmt (piSpec), facts):: rest -> 
    (
    match (piCondition, piSpec) with 
    | (Lt(Basic(BSTR(t1)), Basic(BSTR(t2))), Lt(Basic t3, Basic t4)) -> Some ([(t1,t3); (t2, t4)], facts)
    | (Gt(Basic(BSTR(t1)), Basic(BSTR(t2))), Gt(Basic t3, Basic t4)) -> Some ([(t1,t3); (t2, t4)], facts)
    | (GtEq(Basic(BSTR(t1)), Basic(BSTR(t2))), GtEq(Basic t3, Basic t4)) -> Some ([(t1,t3); (t2, t4)], facts)
    | (LtEq(Basic(BSTR(t1)), Basic(BSTR(t2))), LtEq(Basic t3, Basic t4)) -> Some ([(t1,t3); (t2, t4)], facts)
    | (Eq(Basic(BSTR(t1)), Basic(BSTR(t2))), Eq(Basic t3, Basic t4)) -> Some ([(t1,t3); (t2, t4)], facts)
    | _ -> findIfStmtSpecFrom rest piCondition
    )

  | _ :: rest -> findIfStmtSpecFrom rest piCondition    
  ;;


let string_of_decl (decl:Clang_ast_t.decl) : string = 
  match decl with
  | Clang_ast_t.VarDecl (_, a , _, _) -> 
  (*Clang_ast_proj.get_decl_kind_string*) a.ni_name 
  | _ -> Clang_ast_proj.get_decl_kind_string decl


let rec var_binding (formal:string list) (actual: basic_type list) : bindings = 
  match (formal, actual) with 
  | (x::xs, v::ys) -> (x, v) :: (var_binding xs ys)
  | _ -> []
  ;;


let computeRange intList = 
  match intList with 
  | [] -> (0, 10000000)
  | x :: xs  -> 
    List.fold_left xs ~init:(x, x) 
    ~f:(fun (min, max) a -> 
      if a < min then (a, max) 
      else if a > max then (min, a)
      else (min, max)) 

 


let rec getLastEle (li:basic_type list) :  basic_type option  = 
  match li with 
  | [] -> None 
  | [l] -> Some l 
  | _ :: xs -> getLastEle xs 

let rec lastLocOfFact (facts: fact list) = 
  match facts with 
  | [] -> [] 
  | (str, argLi) :: xs  -> 
    if String.compare str flowKeyword == 0 then lastLocOfFact xs  
    else 
    (match getLastEle argLi with 
    | Some (BINT i) -> i :: (lastLocOfFact xs)
    | _ -> lastLocOfFact xs 
    )




let syhtrim str =
  if String.compare str "" == 0 then "" else
  let search_pos init p next =
    let rec search i =
      if p i then raise(Failure "empty") else
      match str.[i] with
      | ' ' | '\n' | '\r' | '\t' -> search (next i)
      | _ -> i
    in
    search init
  in
  let len = String.length str in
  try
    let left = search_pos 0 (fun i -> i >= len) (succ)
    and right = search_pos (len - 1) (fun i -> i < 0) (pred)
    in
    String.sub str left (right - left + 1)
  with
  | Failure "empty" -> ""
;;

let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (syhtrim line) :: input_lines file
  | _ -> assert false 
;;


let retriveComments (source:string) : (string list) = 
  (*print_endline (source); *) 
  let partitions = Str.split (Str.regexp "/\*@") source in 
  (* print_endline (string_of_int (List.length partitions)); *)
  match partitions with 
  | [] -> assert false 
  | _ :: rest -> (*  SYH: Note that specification can't start from line 1 *)
  let partitionEnd = List.map rest ~f:(fun a -> Str.split (Str.regexp "@\*/")  a) in 
  let rec helper (li: string list list): string list = 
    match li with 
    | [] -> []
    | x :: xs  -> 
      (match List.hd x with
      | None -> helper xs 
      | Some head -> 
        if String.compare head "" ==0 then helper xs 
        else 
          let ele = ("/*@" ^ head ^ "@*/") in 
          (ele :: helper xs)  ) 
  in 
  let temp = helper partitionEnd in 
  temp
  

(* lines of code, lines of sepc, number_of_protocol *)
let retriveSpecifications (source:string) : (ctl list * int * int * int) = 
  let ic = open_in source in
  try
      let lines =  (input_lines ic ) in
      let rec helper (li:string list) = 
        match li with 
        | [] -> ""
        | x :: xs -> x ^ "\n" ^ helper xs 
      in 
      let line = helper lines in
      
      let line_of_code = List.length lines in 
      let partitions = retriveComments line in (*in *)
      let line_of_spec = List.fold_left partitions ~init:0 ~f:(fun acc a -> acc + (List.length (Str.split (Str.regexp "\n") a)))  in 
      (* (if List.length partitions == 0 then ()
      else print_endline ("Global specifictaions are: "));
      *)
      let sepcifications = List.map partitions 
        ~f:(fun singlespec -> 
          (*print_endline (singlespec);*)
          Parser.ctl Lexer.token (Lexing.from_string singlespec)) in      

      (sepcifications, line_of_code, line_of_spec, List.length partitions)
      (*
      
      print_string (List.fold_left (fun acc a -> acc ^ forward_verification a progs) "" progs ) ; 
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)
      *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;



let int_of_optionint intop = 
  match intop with 
  | None  -> (-1)
  | Some i -> i ;;



let retrive_basic_info_from_AST ast_decl: (string * Clang_ast_t.decl list * ctl list * int * int * int) = 
    match ast_decl with
    | Clang_ast_t.TranslationUnitDecl (decl_info, decl_list, _, translation_unit_decl_info) ->
        let source =  translation_unit_decl_info.tudi_input_path in 
        let (specifications, lines_of_code, lines_of_spec, number_of_protocol) = retriveSpecifications source in 
        (source, decl_list, specifications, lines_of_code, lines_of_spec, number_of_protocol)
 
    | _ -> assert false

let getNodeID node : int  = 
  (* Here is to get the ID, which is unique *)
  let key = (string_of_int (Procdesc.Node.get_id node)) in
  (* Simplification of the identifiers *)
  match IDM.find !node_map key with
  | Some(x) -> x
  | None -> let v = !node_val in 
    incr node_val; 
    let k = v 
    in node_map:= IDM.set !node_map ~key:key ~data:k ; k 


let get_facts procedure =
  let out_c = Out_channel.create "zprint" in
  let fmt = F.formatter_of_out_channel out_c in

  let process acc (node: Procdesc.Node.t) = 
    let flows, facts = acc in 

    let node_loc = 
        let loc = (Procdesc.Node.get_loc node) in
        Printf.sprintf "@%s" (Location.to_string loc)
    in
    let node_key =  Int.to_string (getNodeID node) in
    let node_kind = Procdesc.Node.get_kind node in
    let instructions = 
      (Instrs.fold (Procdesc.Node.get_instrs node) ~init:[] 
      ~f:(fun acc ins -> 
        acc @ (match ins with 
        | Load l -> [Printf.sprintf "ILoad(%s,%s)" (Exp.to_string l.e) (Ident.to_string l.id)]
        | Store s -> [Printf.sprintf "IStore(%s,%s)" (Exp.to_string s.e1) (Exp.to_string s.e2)]
        | Prune (e, loc, f, _) -> [(Printf.sprintf "Prune(%s, %b)" (Exp.to_string e) f)]
        | Call ((ret_id, _), e_fun, arg_ts, _, _)  -> 
          let args = (String.concat ~sep:"," (List.map ~f:(fun (x,y) -> Exp.to_string x) arg_ts)) in
            [Printf.sprintf "ICall(%s,%s,%s)" (Exp.to_string e_fun) args (Ident.to_string ret_id) ]
        | Metadata _ -> [] (* "IMetadata"  *)
        ) 
        
              
      ))  in
    let instrs =  (String.concat ~sep:"," instructions) in  
    let succs = (Procdesc.Node.get_succs node) in
    let node_facts =
    match node_kind with
      | Start_node -> [
        (Printf.sprintf "Start(%s). // %s" node_key node_loc);
        ]
      | Exit_node ->  [
        (Printf.sprintf "Exit(%s).  // %s" node_key node_loc);
        ]
      | Join_node ->  [
        (Printf.sprintf "%s(%s,[%s]).  // %s" joinNodeKeyWord node_key instrs node_loc);
        ] 
      | Skip_node t ->  [
        (Printf.sprintf "Skip(%s,%s,[%s]).  // %s" node_key t instrs node_loc);
        ] 
      | Prune_node (f,_,_) ->  [
        (Printf.sprintf "PruneNode(%s,%b,[%s]). // %s" node_key f instrs node_loc);
        ]
      | Stmt_node stmt_kind -> 
        
        let info = match stmt_kind with 
        | AssertionFailure ->  (Printf.sprintf "Stmt_AssertionFailure(%s,[%s]). // %s" node_key instrs node_loc)
        | AtomicCompareExchangeBranch -> (Printf.sprintf "Stmt_AtomicCompareExchangeBranch(%s,[%s]). // %s" node_key instrs node_loc)
        | AtomicExpr -> (Printf.sprintf "Stmt_AtomicExpr(%s,[%s]). // %s" node_key instrs node_loc)
        | BetweenJoinAndExit -> (Printf.sprintf "Stmt_BetweenJoinAndExit(%s,[%s]). // %s" node_key instrs node_loc)
        | BinaryConditionalStmtInit -> (Printf.sprintf "Stmt_BinaryConditionalStmtInit(%s,[%s]). // %s" node_key instrs node_loc)
        | BinaryOperatorStmt (x)  -> (Printf.sprintf "Stmt_BinaryOperatorStmt(%s,%s,[%s]). // %s" node_key x instrs node_loc)
        | CallObjCNew -> (Printf.sprintf "Stmt_CallObjCNew(%s,[%s]). // %s" node_key instrs node_loc)
        | CaseStmt -> (Printf.sprintf "Stmt_CaseStmt(%s,[%s]). // %s" node_key instrs node_loc)
        | ClassCastException -> (Printf.sprintf "Stmt_ClassCastException(%s,[%s]). // %s" node_key instrs node_loc)
        | CompoundStmt -> (Printf.sprintf "Stmt_CompoundStmt(%s,[%s]). // %s" node_key instrs node_loc)
        | ConditionalStmtBranch -> (Printf.sprintf "Stmt_ConditionalStmtBranch(%s,[%s]). // %s" node_key instrs node_loc)
        | ConstructorInit -> (Printf.sprintf "Stmt_ConstructorInit(%s,[%s]). // %s" node_key instrs node_loc) 
        | CXXDynamicCast -> (Printf.sprintf "Stmt_CXXDynamicCast(%s,[%s]). // %s" node_key instrs node_loc)
        | CXXNewExpr -> (Printf.sprintf "Stmt_CXXNewExpr(%s,[%s]). // %s" node_key instrs node_loc)
        | CXXStdInitializerListExpr -> (Printf.sprintf "Stmt_CXXStdInitializerListExpr(%s,[%s]). // %s" node_key instrs node_loc)
        | MessageCall (x) -> (Printf.sprintf "Stmt_MessageCall(%s,%s,[%s]). // %s" node_key x instrs node_loc) 
        | Call(x) -> (Printf.sprintf "Stmt_Call(%s,%s,[%s]). // %s" node_key x instrs node_loc) 
        | ReturnStmt -> (Printf.sprintf "Stmt_Return(%s,[%s]). // %s" node_key instrs node_loc) 
        | DeclStmt -> (Printf.sprintf "Stmt_Decl(%s,[%s]). // %s" node_key instrs node_loc) 
        | UnaryOperator -> (Printf.sprintf "Stmt_UnaryOperator(%s,[%s]). // %s" node_key instrs node_loc) 
        | CXXTemporaryMarkerSet
        | CXXTry
        | CXXTypeidExpr
        | DefineBody
        | Destruction _
        | Erlang
        | ErlangCaseClause
        | ErlangExpression
        | ExceptionHandler
        | ExceptionsSink
        | ExprWithCleanups
        | FinallyBranch
        | GCCAsmStmt
        | GenericSelectionExpr
        | IfStmtBranch
        | InitializeDynamicArrayLength
        | InitListExp
        | LoopBody
        | LoopIterIncr
        | LoopIterInit
        | MethodBody
        | MonitorEnter
        | MonitorExit
        | ObjCCPPThrow
        | ObjCIndirectCopyRestoreExpr
        | OutOfBound
        | Scope _
        | Skip _
        | SwitchStmt
        | ThisNotNull
        | Throw
        | ThrowNPE -> 
          (*Procdesc.Node.pp_stmt fmt stmt_kind ; *)
          (Printf.sprintf "Stmt_Other(%s). //%s" node_key node_loc)
      in

        [info]
    in


    let create_edge succ = 
      let succ_key = Int.to_string (getNodeID succ) in
      let succ_loc = (Location.to_string (Procdesc.Node.get_loc succ)) in 
      (Printf.sprintf "Flow(%s,%s). //%s-%s" node_key succ_key node_loc succ_loc);
    in
    List.append flows (List.map succs ~f:create_edge), (List.append facts node_facts)
    (* (List.fold (List.map succs ~f:create_edge) ~init:(List.append facts node_facts) ~f:List.append) *)
  in 

  let header = (Printf.sprintf "//-- Facts for Procedure <%s> \n" (Procname.to_string (Procdesc.get_proc_name procedure))) in 
  let finalFlow, finialFacts = (Procdesc.fold_nodes procedure ~init:([], []) ~f:process) in 
  header:: (List.rev finalFlow) @ finialFacts

let rec existStack stack stackIn (t:string) : Exp.t option = 
  match stackIn with 
  | [] -> None 
  | (exp, ident) :: xs  -> 
    if String.compare t (Ident.to_string ident) == 0 
    then 
      let eName = (Exp.to_string exp ) in 
      (match exp with 
      | Lfield (root, field, rest) -> 
        let eNameRoot = (Exp.to_string root ) in 
        let fName = Fieldname.to_string field in  
        if String.compare "n$" (String.sub eNameRoot 0 2 ) == 0 
        then 
          (match existStack stack stack eNameRoot with 
          | None -> Some exp
          | Some exp1 -> Some (Lfield (exp1, field, rest))
          )
          
        else Some exp
      | _ -> 
      if String.compare "n$" (String.sub eName 0 2 ) == 0 
      then existStack stack stack eName
      else Some exp)
    else  existStack stack xs t

let rec expressionToTerm (exp:Exp.t) stack : terms option  = 
  match exp with 
  | Var t -> 
    let tName = (Ident.to_string t) in 
    (*print_endline ("!!!expressionToTerm tName " ^ tName) ; *)
    (match existStack stack stack tName with 
    | Some (Lvar t) -> Some(Basic (BSTR (Pvar.to_string t ))) (** Pure variable: it is not an lvalue *)
    | Some exp -> Some(Basic (BSTR (Exp.to_string exp )))
    | None  ->  Some (Basic (BSTR tName)) (** Pure variable: it is not an lvalue *)
    )
  | Lvar t -> Some (Basic (BSTR (Pvar.to_string t)))  (** The address of a program variable *)

  | Const t ->  (** Constants *)
    (match t with 
    | Cint i -> Some(Basic (BINT (IntLit.to_int_exn i )))  (** integer constants *)
    | _ -> (*Basic BNULL*) None 
    )

  | UnOp (_, t, _) -> 
    (match expressionToTerm t stack with 
    | Some (Basic (BINT n)) -> Some(Basic (BINT ((-1) * n)))
    | _ -> None (*Basic (BSTR ("UnOp1"))*)
    )
    



  | BinOp (Shiftrt, e1, e2)
  | BinOp (MinusA _, e1, e2)
  | BinOp (MinusPI, e1, e2)
  | BinOp (MinusPP, e1, e2) -> 
    let t1 = expressionToTerm e1 stack in 
    let t2 = expressionToTerm e2 stack in 
    (match t1, t2 with 
    | Some t1 , Some t2 -> Some (Minus (t1, t2))
    | _, _  -> None )


    
  | BinOp (Shiftlt, e1, e2)
  | BinOp (PlusA _, e1, e2)
  | BinOp (PlusPI, e1, e2) -> 
    let t1 = expressionToTerm e1 stack in 
    let t2 = expressionToTerm e2 stack in 
    (match t1, t2 with 
    | Some t1 , Some t2 -> Some (Plus (t1, t2))
    | _, _  -> None )

  | BinOp _ (*_ -> Basic (BSTR ("BinOp"))*)
  | Exn _ (*-> Basic (BSTR ("Exn"))*)
  | Closure _ (*-> Basic (BSTR ("Closure"))*)
  | Cast _ (*-> Basic (BSTR ("Cast"))*)
  | Lfield _ (*-> Basic (BSTR ("Lfield"))*)
  | Lindex _ (*-> Basic (BSTR ("Lindex"))*)
  | Sizeof _ -> None (*Basic (BSTR ("Sizeof"))*)

let rec expressionToPure (exp:Exp.t) stack: pure option = 
  (*print_endline ("expressionToPure : " ^ (Exp.to_string exp)); *)
  match exp with 
  | BinOp (Eq, BinOp (Mod _, e1, e2), e3) ->  
    let t1 = expressionToTerm e1 stack in 
    let t2 = expressionToTerm e2 stack in 
    let t3 = expressionToTerm e3 stack in 
    (match (t1, t2,  t3) with 
    | Some (Basic(BSTR var )), Some(Basic (BINT 2)), Some(Basic (BINT 0)) -> Some (Predicate(evenKeyWord, [Basic(BSTR var )])) 
    | Some(Basic(BSTR var )), Some(Basic (BINT 2)), Some (Basic (BINT 1)) -> Some (Predicate(oddKeyWord, [Basic(BSTR var )])) 
    | _ -> None 
    )
  | BinOp (Ne, BinOp (Mod _, e1, e2), e3) ->  
    let t1 = expressionToTerm e1 stack in 
    let t2 = expressionToTerm e2 stack in 
    let t3 = expressionToTerm e3 stack in 
    (match (t1, t2,  t3) with 
    | Some(Basic(BSTR var )), Some(Basic (BINT 2)), Some(Basic (BINT 0)) -> Some (Predicate(oddKeyWord, [Basic(BSTR var )])) 
    | Some(Basic(BSTR var )), Some(Basic (BINT 2)), Some(Basic (BINT 1)) -> Some (Predicate(evenKeyWord, [Basic(BSTR var )])) 
    | _ -> None 
    )


  | BinOp (bop, e1, e2) -> 

    let t1 = expressionToTerm e1 stack in 
    let t2 = expressionToTerm e2 stack in 
    (match t1, t2 with 
    | None, _
    | _, None -> None 
    | Some t1 , Some t2 -> 
      let t2 = 
      match t2 with 
      | (Minus(t2, _ )) -> t2 
      | (t2) -> t2 
      in 
      (match bop with 
      | Eq  -> Some (Eq (t1, t2))
      | Lt -> Some (Lt (t1, t2))
      | Gt -> Some (Gt (t1, t2))
      | Le -> Some (LtEq (t1, t2))
      | Ge -> Some (GtEq (t1, t2))
      | Ne -> Some (Neg (Eq (t1, t2)))
      | LAnd | BAnd -> 
        (match expressionToPure e1 stack, expressionToPure e2 stack with 
        | Some p1, Some p2 -> Some (PureAnd (p1, p2))
        | Some p, None | None, Some p -> Some p 
        | _ -> None 
        )
      | LOr | BOr | BXor -> 
        (match expressionToPure e1 stack, expressionToPure e2 stack with 
        | Some p1, Some p2 -> Some (PureOr (p1, p2))
        | Some p, None | None, Some p -> Some p 
        | _ -> None 
        )
      | Shiftrt -> Some (Eq (t1, Minus(t1, t2)))
      | _ -> 
        (*print_endline ("expressionToPure None : " ^ Exp.to_string exp); *)
        None
      ))

  

  | UnOp (_, e, _) -> 
    (match expressionToPure e stack with 
    | Some p -> Some (normalise_pure (Neg p))
    | None -> 
     print_endline ("expressionToPure UnOp : " ^ Exp.to_string exp ); 

        (match expressionToTerm e stack with 
        | Some t -> Some (Eq (t,  Basic (BINT 0)))
        | None -> 
        None 
        )
  
    )
  | Const _ -> 
    if String.compare (Exp.to_string exp) "1" == 0 then Some TRUE
    else 
      (
      print_endline ("expressionToPure Const : " ^ Exp.to_string exp ); 
      None )

  | Lvar _ 
  | Var _ -> 
    (match expressionToTerm exp stack with 
    | Some t -> Some (Neg (Eq (t,  Basic (BINT 0))))
    | None -> None 
    )
  

      
  (*

  print_endline ("expressionToPure Var None : " ^ Exp.to_string exp); 
      None 
  | Exn _ -> 
    print_endline ("expressionToPure Exn None : " ^ Exp.to_string exp); 
    None 
  | Closure _ -> 
    print_endline ("expressionToPure Closure None : " ^ Exp.to_string exp); 
    None 

  | Cast _ -> 
    print_endline ("expressionToPure Cast None : " ^ Exp.to_string exp); 
    None 
  | Lvar _ -> 
    print_endline ("expressionToPure Lvar None : " ^ Exp.to_string exp); 
    None 
  | Lfield _ -> 
    print_endline ("expressionToPure Lfield None : " ^ Exp.to_string exp); 
    None 
      (** A field offset, the type is the surrounding struct type *)
  | Lindex  _ -> 
    print_endline ("expressionToPure Lindex None : " ^ Exp.to_string exp); 
    None 
  | Sizeof  _ -> 
    print_endline ("expressionToPure Sizeof None : " ^ Exp.to_string exp); 
    None 
    *)
  | _ -> 
    (
    None )
  
let getPureFromFunctionCall (e_fun:Exp.t) (arg_ts:(Exp.t * Typ.t) list) ((Store s):IR.Sil.instr) stack : pure option =
  let exp1 = s.e1 in 
  let temp = expressionToTerm exp1 stack in 
  match temp with 
  | None -> None 
  | Some temp -> 
    let funName = (Exp.to_string e_fun) in 
    if existAux (fun a b -> String.compare a b == 0) nonDetermineFunCall funName then 
      Some (Eq (temp, Basic(ANY)))
    else 
      (*let argumentTerms =  List.map arg_ts ~f:(fun (eA, _) -> expressionToTerm eA stack) in *)
      (* Predicate(funName, argumentTerms) *)
      Some (Eq (temp, Basic(ANY)))



let rec getPureFromBinaryOperatorStmtInstructions (op: string) (instrs:Sil.instr list) stack : pure option = 
  
  if String.compare op "Assign" == 0 then 
    match instrs with 
    | Store s :: _ -> 
      print_endline ("Store: " ^  Exp.to_string s.e1 ^ " = " ^ Exp.to_string s.e2); 
      let exp1 = s.e1 in 
      let exp2 = s.e2 in 
      (match expressionToTerm exp1 stack, expressionToTerm exp2 stack with 
      | Some e1, Some e2 -> 
        Some (Eq (e1, e2))
      | _, _ -> 
      None 
      
      )
      
    | Load l :: tail ->
      let stack' = (l.e, l.id):: stack in 
      getPureFromBinaryOperatorStmtInstructions "Assign" tail stack'    
    | Call ((ret_id, _), e_fun, arg_ts, _, _)  :: Store s :: _ -> 
      (*print_endline (Exp.to_string e_fun) ;   *)
      getPureFromFunctionCall e_fun arg_ts (Store s) stack
    
    | _ -> None 
  else if String.compare op "SubAssign" == 0 || String.compare op "AddAssign" == 0 then  
    match instrs with 
    | Store s :: _ ->  
      getPureFromBinaryOperatorStmtInstructions "Assign" instrs stack
    | Load l :: tail ->
      let stack' = (l.e, l.id):: stack in 
      print_endline ("SubAssign: " ^ string_of_stack stack');
      getPureFromBinaryOperatorStmtInstructions "SubAssign" tail stack'

    | _ -> None 
  else None

let string_of_instruction (ins:Sil.instr) : string = 
  match ins with 
  | Load _ -> "Load"
  | Store _ -> "Store"
  | Prune _ -> "Prune"
  | Call _ -> "Call"
  | Metadata _ -> "Metadata"


  
let rec getPureFromDeclStmtInstructions (instrs:Sil.instr list) stack : pure option = 
  (*print_endline ("getPureFromDeclStmtInstructions: " ^ string_of_int (List.length instrs));
  print_endline (List.fold instrs ~init:"" ~f:(fun acc a -> acc ^ "," ^ string_of_instruction a)); 
  *)
  match instrs with 
  | Store s :: _ -> 
    (*print_endline (Exp.to_string s.e1 ^ " = " ^ Exp.to_string s.e2); *)
    let exp1 = s.e1 in 
    let exp2 = s.e2 in 
    let t1 = expressionToTerm exp1 stack in 
    let t2 = expressionToTerm exp2 stack in 
    (match t1, t2 with 
    | Some (Basic(BSTR a )) , Some (Basic(BINT b )) -> Some (Eq (Basic(BSTR a ), Basic(BINT b )))
    | Some (Basic(BSTR a )) , Some (Basic(BINT b )) -> Some (Eq (Basic(BSTR a ), Basic(BINT b )))
    (*
    | _ -> Some (Eq (t1, Basic ANY))  *)
    (* if it is temp=user_quota_size-quota_size, temp will be ANY *)
    | Some t1, Some t2 -> Some (Eq (t1, t2)) 
    | _, _ -> None 

    )  
    
  | Load l :: tail ->
    let stack' = (l.e, l.id):: stack in 
    getPureFromDeclStmtInstructions tail stack'

  | Call ((ret_id, _), e_fun, arg_ts, _, _)  :: Store s :: _ -> 
    (*print_endline (Exp.to_string e_fun) ;   *)
    getPureFromFunctionCall e_fun arg_ts (Store s) stack
    
  | _ -> None

let rec partitionFromLast (li:'a list) : ('a list * 'a list) = 
  match li with
  | [] -> [], []
  | [x] -> [], [x]
  | x::xs -> 
    let li1, li2 = partitionFromLast xs in 
    x::li1, li2

let updateStakeUsingLoads intrs = 
  List.fold_left intrs ~init:[] ~f:(fun acc (ins:Sil.instr) -> 
    match ins with 
    | Load l -> 
            (*print_endline (Exp.to_string l.e ^ " -> " ^ IR.Ident.to_string l.id); *)
            (l.e, l.id) :: acc 
          | _ -> acc
        ) 

let removeDotsInVarName str =
  let str_li =  String.split_on_chars ~on:['.';'&';':'] str in 
  let rec aux li = 
    match li with 
   | [] -> ""
   | [x] -> x
   | x ::xs  -> x ^ "_" ^ aux xs 
   in aux str_li

let regularExpr_of_Node node stack : (regularExpr * stack )= 
  let node_kind = Procdesc.Node.get_kind node in
  let node_key =  getNodeID node in
  let instrs_raw =  (Procdesc.Node.get_instrs node) in  
  let instrs = Instrs.fold instrs_raw ~init:[] ~f:(fun acc (a:Sil.instr) -> 
      match a with 
      | Metadata _ -> acc 
      | _ -> acc @ [a]) 
  in 
  match node_kind with
  | Start_node -> Singleton (Predicate (entryKeyWord, []), node_key), []
  | Exit_node ->  Singleton (Predicate (exitKeyWord, []), node_key), []
  | Join_node ->  (*Singleton(Predicate (joinKeyword, []), node_key)*)Emp , []
  | Skip_node _ ->  Singleton(Predicate (skipKeyword, []), node_key) , []
  | Prune_node (f,_,_) ->  
    let loads, last = partitionFromLast instrs in 
    let stack' = updateStakeUsingLoads loads in 

    
    (match last with 
    | Prune (e, loc, f, _):: _ ->  
      (match expressionToPure e (stack@stack') with 
      | Some p -> 
        let (p':pure) = 
          match p with 
          | Eq (Basic (BSTR v1), t2) -> 
              let v2= removeDotsInVarName v1 in 
              Eq (Basic (BSTR v2), t2)
          | Neg (Eq (Basic (BSTR v1), t2)) -> 
              let v2= removeDotsInVarName v1 in 
              let p':pure = Neg (Eq (Basic (BSTR v2), t2)) in 
              p'

          | (Gt (Basic (BSTR v1), t2)) -> 
              let v2= removeDotsInVarName v1 in 
              let p':pure = (Gt (Basic (BSTR v2), t2)) in 
              p'

          | (LtEq (Basic (BSTR v1), t2)) -> 
              let v2= removeDotsInVarName v1 in 
              let p':pure = (LtEq (Basic (BSTR v2), t2)) in 
              p'

          | (Lt (Basic (BSTR v1), t2)) -> 
              let v2= removeDotsInVarName v1 in 
              let p':pure = (Lt (Basic (BSTR v2), t2)) in 
              p'

          | (GtEq (Basic (BSTR v1), t2)) -> 
              let v2= removeDotsInVarName v1 in 
              let p':pure = (GtEq (Basic (BSTR v2), t2)) in 
              p'



          | _ -> p 

        in 
        Guard(p', node_key)
      | None -> 

        Guard(TRUE, node_key) ), stack'
    | Load l :: Prune (e, loc, f, _):: _ ->  
      let stack' = (l.e, l.id) :: stack in 
      (match expressionToPure e (stack@stack') with 
      | Some p -> Guard(p, node_key)
      | None -> 
        Guard(TRUE, node_key) ), stack'

    | _ -> 
      Singleton(TRUE, node_key) , stack'
    )
  

  | Stmt_node stmt_kind ->         
    match stmt_kind with 
    | BinaryOperatorStmt (op) -> 
      if existAux (fun a b-> String.compare a b ==0) ["EQ";"GT";"LT";"NE";"LE";"GE"] op then 
        (*String.compare op "EQ" == 0 || String.compare op "GT" == 0 then  *)
        let stack = updateStakeUsingLoads instrs in 
        Emp , stack
        (*Singleton(TRUE, node_key), stack *)
        (* This is to avoid th extra (T)@loc before the guard, we only need to 
           record the stack, but no need any event *)

      else if existAux (fun a b-> String.compare a b ==0) ["ShrAssign"] op then 
        let loads, last = partitionFromLast instrs in 
        let stack' = updateStakeUsingLoads loads in 
        match last with 
        | Store s :: _ -> 
          let exp1 = s.e1 in 
          (match expressionToTerm exp1 stack' with 
          | None -> Singleton(TRUE, node_key), []   
          | Some t1 -> 
          
          let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
          let g1 = Guard(Lt(t1, Basic (BINT 0 )), !allTheUniqueIDs) in 
          let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
          let g2 = Guard((Gt(t1, Basic (BINT 0 ))), !allTheUniqueIDs) in 

          Disjunction (Concate(g1, Singleton(Eq(t1, t1), node_key)), Concate(g2, Singleton(Eq(t1, Minus (t1 ,Basic (BINT 1))), node_key)) ), 
          stack' )
        | _ -> Singleton(TRUE, node_key), []   


          
      else 
        (match getPureFromBinaryOperatorStmtInstructions op instrs stack with 
        | Some pure -> Singleton (pure, node_key), []
        | None -> Singleton(TRUE, node_key), [] )  
        
    | UnaryOperator 
    | DeclStmt -> 
      let loads, _ = partitionFromLast instrs in 
      let stack' = updateStakeUsingLoads loads in 

      print_endline ("DeclStmt: " ^ string_of_stack stack');
      (match getPureFromDeclStmtInstructions instrs stack with 
      | Some pure -> Singleton (pure, node_key), stack'
      | None -> Singleton(TRUE, node_key), stack' )

    | ReturnStmt -> 
      (match instrs with 
      | Store s :: _ -> 
        (*print_endline (Exp.to_string s.e1 ^ " = " ^ Exp.to_string s.e2); *)
        let exp2 = s.e2 in 
        (*predicateDeclearation:= (retKeyword, ["Number";"Number"]) :: !predicateDeclearation ;
        *)
        (match expressionToTerm exp2 stack with
        | Some t -> Singleton (Predicate (retKeyword, [t]), node_key), []
        | _ ->  Singleton (Predicate (retKeyword, []), node_key), []
        )

      | _ -> 
        Singleton (Predicate (retKeyword, [Basic(BINT 0)]), node_key), []
      )
    | Call x  -> 
      (match instrs with 
      | Call ((ret_id, _), e_fun, arg_ts, _, _)  :: _ -> 
        let (argumentTerms:terms list) =  List.fold_left arg_ts ~init:[] ~f:(fun acc (eA, _) -> 
          match expressionToTerm eA stack with 
          | Some t -> acc@[t] 
          | None -> acc 
        ) in 
        let argumentTermsType = List.map argumentTerms 
          ~f:(fun a -> 
          match a with 
          |  (Basic(BINT _ )) ->"Number" 
          |  (Basic(BSTR _ )) -> "Symbol" 
          |  (Basic(BSTR _ )) -> "Symbol" 
          | _ -> "")  in 
        let funName = (Exp.to_string e_fun) in 
        let funName = String.sub funName 5 (String.length funName - 5) in 
        
        let funName =removeDotsInVarName funName in 

        predicateDeclearation:= (funName, argumentTermsType@["Number"]) :: !predicateDeclearation ;
        Singleton (Predicate (funName, argumentTerms), node_key), [] 
       
      | _ -> 
        let funName = String.sub x 5 (String.length x - 5) in 
        let funName =removeDotsInVarName funName in 

        Singleton (Predicate (funName, []), node_key), []
      )
    
      
    | _ -> Singleton(TRUE, node_key) , []


let rec existRecord (li: Procdesc.Node.t list) n : ((Procdesc.Node.t list) * (Procdesc.Node.t list)) option = 
  match li with 
  | [] ->  None 
  | x :: xs  -> 
    if (getNodeID x) == n 
    then Some ([], li)
    else 
      match existRecord xs n with 
      | None -> None 
      | Some (prefix, cycle) -> 
        Some (x::prefix, cycle)



let rec disjunctRE (li:regularExpr list): regularExpr = 
  match li with 
  | [] -> Bot 
  | [x] -> x 
  | x :: xs -> 
    let x = normalise_es x in 
    let rest = normalise_es (disjunctRE xs) in 
    (*
    print_endline (string_of_regularExpr x);
    print_endline (string_of_regularExpr rest);
    print_endline ("========");   
    *)


    (match x, rest with 
    | Kleene(re1), Kleene(re2) -> 
        (*
        print_endline (string_of_regularExpr re1);
        print_endline (string_of_regularExpr re2);
        print_endline ("~~~~~");
        *)


      (match fst re1, fst re2 with 
      | [f1], [f2] -> 
        (*
        print_endline (string_of_fst_event f1);
        print_endline (string_of_fst_event f2);
        print_endline ("~~~~~");   
        *)

        if compareEvent f1 f2 then Kleene(normalise_es(Disjunction(re1, re2)))
        else Disjunction (x, disjunctRE xs)
      | _ -> Disjunction (x, disjunctRE xs)
      )
    | _ -> Disjunction (x, disjunctRE xs)
    )
    
let rec recordToRegularExpr (li:Procdesc.Node.t list) stack : (regularExpr * stack) = 
  match li with 
  | [] -> Emp, []
  | [currentState] -> regularExpr_of_Node currentState stack
  | currentState :: xs  -> 
    let eventHd, stack' = regularExpr_of_Node currentState stack in 
    let eventTail, stack'' = recordToRegularExpr xs (stack@stack') in 
    Concate(eventHd, eventTail), (stack@stack'@stack'')


let rec existCycleHelper stack (currentState:Procdesc.Node.t) (id:state list) : (regularExpr * stack * bool)  = 
  let node_kind = Procdesc.Node.get_kind currentState in
  let currentID = getNodeID currentState in
  
  
  (*print_endline ("existCycleHelper stack: " ^ string_of_stack stack);*)
  (*
  print_endline ("id:\n" ^  List.fold_left ~init:"" id ~f:(fun acc a -> acc ^ string_of_int (a))); 
  print_endline ("existCycleHelper id: " ^ string_of_int currentID);
  *)
  let idHead, idTail = 
    match id with 
    | [] -> raise (Failure "existCycleHelper not possible")
    | hd::tail -> hd, tail
  in 



  let moveForward_aux stackCtx (nodeIn:Procdesc.Node.t): (regularExpr * stack * bool)  =
    let reExtensionIn, stackIn = recordToRegularExpr ([nodeIn]) stackCtx in  
    let nextStates = Procdesc.Node.get_succs nodeIn in 
    match nextStates with 
    | [] -> 
      (reExtensionIn, stackCtx@stackIn, false)
    
   
    | [succ] -> 
      (match existCycleHelper (stackCtx@stackIn) succ id with 
      | (re, stackSucc, false) -> (Concate(reExtensionIn, re), stackCtx@stackIn@stackSucc, false) 
      | (re, stackSucc, true) -> (Concate(reExtensionIn, re), stackCtx@stackIn@stackSucc, true)
      )
    | succ1::succ2::_ -> 
      (match existCycleHelper  (stackCtx@stackIn) succ1 id, existCycleHelper  (stackCtx@stackIn) succ2 id with 
      | (re1, stackSucc1, false), (re2, stackSucc2, false) -> (Concate(reExtensionIn, Disjunction(re1, re2)), stackCtx@stackIn@stackSucc1@stackSucc2, false) 
      | (re1, stackSucc1, false), (re2, stackSucc2, true)
      | (re1, stackSucc1, true), (re2, stackSucc2, false)
      | (re1, stackSucc1, true), (re2, stackSucc2, true) -> (Concate(reExtensionIn, Disjunction(re1, re2)), stackCtx@stackIn@stackSucc1@stackSucc2, true)
      )

  in 

  if currentID == idHead then (Emp, stack, true)
  else if existAux (==) idTail currentID then (Emp, stack, false)

  else 
    match node_kind with 
    | Join_node -> 
      (match existCycle stack currentState (currentID::id) with 
      | Some (non_cycle_succ, loop_body, stack1) -> 
        (*print_endline ("loop_body1: " ^ string_of_regularExpr loop_body); *)
        let re1Succ, stackSucc, flag = moveForward_aux (stack@stack1) non_cycle_succ in  
       (Disjunction(re1Succ, Kleene(loop_body)), stack@stack1@stackSucc, flag)
      | None -> moveForward_aux stack currentState
      )
    | _ -> moveForward_aux stack currentState





and existCycle stack (currentState:Procdesc.Node.t) (id:state list) : (Procdesc.Node.t * regularExpr * stack) option = 
  
  (*
  print_endline ("existCycl:\n" ^ string_of_int (getNodeID currentState)); 
  print_endline ("id:\n" ^  List.fold_left ~init:"" id ~f:(fun acc a -> acc ^ string_of_int (a))); 
  *)

  let reExtension, stack' = recordToRegularExpr ([currentState]) stack in 


  let nextStates = Procdesc.Node.get_succs currentState in 
  match nextStates with 
  | [succ] -> 
    
    if List.length (Procdesc.Node.get_succs succ) == 1 then None 
    else 
    (match Procdesc.Node.get_kind succ with 
    | Join_node -> None 
    | _ -> 
      (match existCycle (stack'@stack) succ id with 
      | None -> None 
      | Some (node, re, stack'') -> Some (node, Concate(reExtension, re), stack@stack'@stack'')
      
      )
    )

    
  | [succ1;succ2] -> 
    let trueNodefalseNode = 
      (match (Procdesc.Node.get_kind succ1, Procdesc.Node.get_kind succ2) with 
      | (Prune_node(true, _, _), Prune_node(false, _, _)) -> Some (succ1, succ2)
      | (Prune_node(false, _, _), Prune_node(true, _, _)) -> Some (succ2, succ1)
      | _ -> None
      )
    in 
    (match  trueNodefalseNode with 
    | None -> None 
    | Some (trueNode, falseNode) -> 
      (match existCycleHelper (stack@stack') trueNode id with 
      | (_, _, false) -> None 
      | (re, stack'', true) -> Some (falseNode, re, stack@stack'@stack'')
      )
  )
    
  | _ -> None 

  


let rec getRegularExprFromCFG_helper_new stack (currentState:Procdesc.Node.t): (regularExpr * stack) = 
  let node_kind = Procdesc.Node.get_kind currentState in
  let currentID = getNodeID currentState in
  (*print_endline ("getRegularExprFromCFG_helper_new:\n" ^ string_of_int currentID); 
  *)

  let moveForward stackCtx (nodeIn:Procdesc.Node.t): (regularExpr * stack)  = 
    let reExtensionIn, stackIn = recordToRegularExpr ([nodeIn]) stackCtx in 

    let stack'' = (stackIn@stackCtx) in 
    let nextStates = Procdesc.Node.get_succs nodeIn in 
    match nextStates with 
    | [] -> (reExtensionIn , stack'')
    | [succ] ->  
      let re1Succ, stackSucc= getRegularExprFromCFG_helper_new stack'' succ in 
      Concate (reExtensionIn, re1Succ), (stack''@stackSucc)

    | succ1::succ2::_ -> 
      let re1Succ1, stackSucc1 = getRegularExprFromCFG_helper_new stack'' succ1 in 
      let re1Succ2, stackSucc2 = getRegularExprFromCFG_helper_new stack'' succ2 in 
      Concate (reExtensionIn, Disjunction(re1Succ1, re1Succ2)), (stack''@stackSucc1@stackSucc2)
  in 

  (match node_kind with 

  | Exit_node | Stmt_node ReturnStmt -> (* looping at the last state *)
    let reExtension, stack' = recordToRegularExpr ([currentState]) stack in 
    ((reExtension), (stack@stack'))
  | Join_node ->
    (match existCycle stack currentState [currentID] with 
    | Some (non_cycle_succ, loop_body, stack1) -> 
      (*print_endline ("loop_body2: " ^ string_of_regularExpr loop_body); *)
      let re1Succ, stackSucc = moveForward (stack@stack1) non_cycle_succ in  
      Disjunction(re1Succ, Kleene(loop_body)), (stack@stack1@stackSucc)
    | None -> moveForward stack currentState
    )
  | _ -> moveForward stack currentState
  )


let getRegularExprFromCFG (procedure:Procdesc.t) : regularExpr = 
  let startState = Procdesc.get_start_node procedure in 
  (*
  let reoccurs = sort_uniq (-) (findReoccurrenceJoinNodes [] startState) in    
  let _ = List.map reoccurs ~f:(fun a -> print_endline ("reoccurrance" ^ string_of_int a)) in  *)
  (*let r, _ = getRegularExprFromCFG_helper reoccurs Emp [] startState in *)
  let r, _ = getRegularExprFromCFG_helper_new [] startState in 
  r


let rec normaliseTheDisjunctions (re:regularExpr) : regularExpr = 
  let (fstSet:(fstElem list)) = fst re in 
  let fstSet' = removeRedundant fstSet compareEvent in 
  (*
  print_endline (" ============ \n" ^ string_of_regularExpr re ^ ":\n"); 
  print_endline (List.fold_left fstSet ~init:"" ~f:(fun acc a -> acc ^ ", " ^  (string_of_fst_event a)) ^ "\n");
  print_endline (List.fold_left fstSet' ~init:"" ~f:(fun acc a -> acc ^ ", " ^ (string_of_fst_event a)));
  *)
  match fstSet' with 
  | [] -> normalise_es re     
  | _ -> 
    let disjunctions = List.map fstSet' ~f:(fun f -> 
      let deriv = normalise_es (derivitives f re) in 
      match deriv with 
      | Emp -> eventToRe f
      | _ ->
        Concate (eventToRe f, normaliseTheDisjunctions deriv)
    ) in 
    disjunctRE disjunctions

let rec getAllPathConditions (re:regularExpr): pure list = 
  match re with 
  | Emp | Bot | Singleton _ -> [TRUE]
  | Guard (p, _) -> [(normalise_pure p)]
  | Concate(re1, re2) ->
    let pc1 = getAllPathConditions re1 in 
    let pc2 = getAllPathConditions re2 in 
    let mix = cartesian_product pc1 pc2 in 
    List.map mix ~f:(fun (a, b) -> 
      match a, b with 
      | Ast_utility.TRUE, _ -> b 
      | _, Ast_utility.TRUE -> a 
      | _,  _ -> PureAnd(a, b))
    
  | Disjunction (re1, re2) -> 
    let pc1 = getAllPathConditions re1 in 
    let pc2 = getAllPathConditions re2 in 
    pc1 @ pc2
  | Omega re -> getAllPathConditions re 
  | Kleene _ -> raise (Failure "not possible getAllPathConditions kleene")


let rec makeAGuessFromPureRelaxed (pi:pure) : terms list = 
  match pi with 
  | LtEq (t, Basic (BINT 0)) -> [t] 
  | Lt (t, Basic (BINT 0)) -> [(Plus(t, Basic (BINT 1)))]
  | Lt (t1, t2) -> [(Minus(t2, t1))]
  | Eq (t1, Basic (BINT n)) -> [(Minus(Basic (BINT n), t1)); (Minus(t1, Basic (BINT n)))]
  | GtEq (t, Basic (BINT 0)) 
  | Gt (t, Basic (BINT 0)) ->[ t ]
  | Gt (t1, t2) -> [(Minus(t1, t2))]
  | PureAnd (p1, p2) 
  | PureOr (p1, p2) -> 
    (match makeAGuessFromPureRelaxed p1, makeAGuessFromPureRelaxed p2 with 
    |  t1::_, _ 
    | _,  t1 :: _ ->  [t1]
    | _, _-> [] 
    )
  | _ -> [] 

let rec makeAGuessFromPure (pi:pure) : terms list = 
  match pi with 
  | LtEq (t, Basic (BINT 0)) 
  | Lt (t, Basic (BINT 0)) -> [(Minus(Basic (BINT 0), t))]
  | Lt (t1, t2) -> [ (Minus(t2, t1))]
  | GtEq (t, Basic (BINT 0)) -> [ (Plus(t, Basic (BINT 1)))]
  | Neg (Eq(t, Basic (BINT 0)))
  | Gt (t, Basic (BINT 0)) ->[ t ]
  | Gt (t1, t2) -> [(Minus(t1, t2))]
  | PureAnd (p1, p2) 
  | PureOr (p1, p2) -> 
    (match makeAGuessFromPure p1, makeAGuessFromPure p2 with 
    | t1::_, _ 
    | _,  t1 :: _ ->  [t1]
    | _, _-> [] 
    )
  | _ -> [] 

let rec deleteallGuard (reIn:regularExpr) : regularExpr = 
  match reIn with 
  | Guard(pi, _) -> Emp 
  | Disjunction (re1, re2) ->Disjunction(deleteallGuard re1, deleteallGuard re2)
  | Concate (re1, re2) ->  Concate(deleteallGuard re1, deleteallGuard re2)

  | Omega re1 -> Omega(deleteallGuard re1)
  | Kleene re1 ->  Kleene(deleteallGuard re1)
  | _ -> reIn
  

let rec getPersistantValuation(reIn:regularExpr) : regularExpr = 
  match reIn with 
  | Singleton(Eq(Basic (BSTR a), Basic (BINT n)), _) -> reIn 
  | Guard _ -> Emp 
  | Disjunction (re1, re2) -> Disjunction(getPersistantValuation re1, getPersistantValuation re2)
  | Concate (re1, re2) ->  Concate(getPersistantValuation re1, getPersistantValuation re2)

  | Omega re1 -> Omega(getPersistantValuation re1)
  | Kleene re1 ->  Kleene(getPersistantValuation re1)
  | _ -> reIn


let makeAGuessFromGuard (re:regularExpr) : rankingfunction list = 

  
  let pathConditions = getAllPathConditions re in 
  let pathConditions = flattenList (List.map  pathConditions ~f:decomposePure) in 
  (*print_endline ("makeAGuessFromGuard pathConditions \n" ^ (String.concat ~sep:",\n" (List.map ~f:(fun p -> string_of_pure p) (pathConditions))));   
*)
  let temp = flattenList (List.map pathConditions ~f:makeAGuessFromPureRelaxed)  in 
  List.map temp ~f:(fun a -> (a, 
    Some (deleteallGuard re)))

(* makeAGuess is to get a list of possible ranking functions *)
(* it returns a list of ranking functions, and for the onces derived from the leacking paths, it is together with a regular expression denoting the leacking behaviours  *)
let rec makeAGuess (guard:pure) (terminatingCases) :  rankingfunction list = 
  let r1 = makeAGuessFromPure guard in 
  let r2 = makeAGuessFromGuard terminatingCases in 
  List.map r1 ~f:(fun a -> (a, None)) @ r2 
  


let rec findStateRecord (t:terms) (s:((terms * terms)list)) = 
    match s with 
    | [] -> None 
    | (t1, t2) :: xs -> 
      if stricTcompareTerm t t1 
      then Some (t2, xs)
      else 
        (match findStateRecord t xs  with 
        | None  -> None 
        | Some (t', xs) -> Some (t', (t1, t2)::xs) 
        )   
;;
  
let rec computePostRankingFunctionFromTransitionSUmmary (t:terms) (s:((terms * terms)list)) :  terms= 
  match t with 
  | Minus(t1, t2) -> Minus(computePostRankingFunctionFromTransitionSUmmary t1 s, computePostRankingFunctionFromTransitionSUmmary t2 s)
  | Plus (t1, t2) -> Plus(computePostRankingFunctionFromTransitionSUmmary t1 s, computePostRankingFunctionFromTransitionSUmmary t2 s)
  | Basic _ -> 
    (match findStateRecord t s with 
    | None  -> t 
    | Some (t', _) -> t')
   
 
;;

let updateStateBasedOnCurrentValues (state:((terms * terms)list)) (target:terms) (newValue:terms) : ((terms * terms)list) = 
  let rec subsititude (t:terms) : terms = 
    match findStateRecord t state with 
    | Some (Basic ANY, _) -> t 
    | Some (t', _) -> t' 
    | None  -> 
      (match t with 
      | Basic _ -> t 
      | Plus (t1, t2) -> Plus (subsititude t1, subsititude t2)
      | Minus (t1, t2) -> Minus (subsititude t1, subsititude t2)

      )
  in 
  let newValue' = subsititude newValue in 
  match findStateRecord target state with 
  | Some (_, rest) -> (target, newValue') :: rest 
  | None -> (target, newValue') :: state
  ;;

let transitionSummary (re:regularExpr) : transitionSummary = 
  print_endline ("transitionSummary input : " ^ string_of_regularExpr re);
  let updateTransitionPath acc pi = List.map acc ~f:(fun (pAcc, state) -> (PureAnd(pAcc, pi), state)) in 
  let updateTransitionStates acc pi = 
    match pi with 
    | Eq (t1, t2) -> 
      let temp = List.map acc ~f:(
      fun (pAcc, state) -> 
        let state' = updateStateBasedOnCurrentValues state t1 t2 in 
        (pAcc, state')) 
      in 
      (*print_endline ("============\n" ^ string_of_transitionSummary acc);
      print_endline ("updateTransitionStates: " ^ string_of_pure pi);
      print_endline (string_of_transitionSummary temp);
      *)
      temp

    | _ -> acc 
  in 
  let rec helper acc reIn : transitionSummary = 
    match reIn with 
    | Emp | Bot -> acc 
    | Singleton (pi, _) -> updateTransitionStates acc pi 
    | Guard(pi, _) -> updateTransitionPath acc pi  
    | Disjunction (re1, re2) ->
      helper acc re1 @ helper acc re2
    | Concate (re1, re2) -> 
      let acc' = helper acc re1 in 
      helper acc' re2
    | Omega _ | Kleene _ -> raise (Failure "there is a cycly inside a cycle")
   
  in 
  helper [(TRUE, [])] re

  ;;

(* devideByExitOrReturn returns two results, one is the terminating traces, ends with return or exit, and 
   the other is non-terminating traces, which needs to decrese with some ranking function  *)
let devideByExitOrReturn (re:regularExpr) : (regularExpr * regularExpr) = 
  let re = normalise_es re in 

  let rec helper (reIn:regularExpr) : (regularExpr * regularExpr) = 
    let fstSet = fst reIn in 
    match fstSet with 
    | [] -> (Bot, Emp) 
    | fLi -> 
      let (res:(regularExpr * regularExpr)) = 
        List.fold_left ~init:(Bot, Bot) ~f:(fun (accTerm, accNonTerm) f -> 
        let (cTerm, cNonTerm) = 
          match f with 
          | PureEv (Predicate (str, _), _) -> 
            if String.compare str retKeyword ==0 || String.compare str  exitKeyWord  ==0 
            then (eventToRe f, Bot)
            else (Bot, eventToRe f) 

          | PureEv _
          | Delimiter _ 
          | GuardEv _ -> (Bot, eventToRe f) 
          | OmegaEv reIn -> (Omega reIn, Bot)
          | _ ->  raise (Failure "devideByExitOrReturn helper Emp | Bot | Omega _ | Kleene _   " )
        in 
        let (dTerm, dNonTerm) = helper (normalise_es(derivitives f reIn)) in 
        let (accTerm', accNonTerm') = 
          match (cTerm, cNonTerm) with 
          | (Bot, fEv) -> (Concate(fEv, dTerm), Concate(fEv, dNonTerm))
          | (fEv, Bot) -> (fEv, Bot)
          | _ , _ -> raise (Failure "devideByExitOrReturn helper no possible  " )
        in 
        (Disjunction(accTerm,  accTerm'), Disjunction(accNonTerm, accNonTerm')) 

      
        ) fLi 
      in res 
  in 
  let term, nonterm =  helper re in 
  normalise_es term, normalise_es nonterm



(* decomposeRE is to enumarate all the disjunctive cases *)
let rec decomposeRE re : regularExpr list = 
  match re with 
  | Disjunction (re1, re2) -> 
    decomposeRE re1 @ decomposeRE re2 
  | Concate (re1, re2) -> 
    let li1 = decomposeRE re1 in 
    let li2 = decomposeRE re2 in 
    let mix = cartesian_product li1 li2 in 
    List.map mix ~f:(fun (a, b) -> Concate(a, b)) 
  | _ -> [re]
  


(* containUnknown is to check is a term contains _, which should not be send to Z3 *)
let rec containUnknown (term:terms) : bool = 
  match term with 
  | Basic ANY -> true 
  | Basic _ -> false 
  | Minus(t1, t2) | Plus(t1,  t2) -> containUnknown t1 || containUnknown t2

let wp4Termination (re:regularExpr) (guard:pure) (rankingFuns:rankingfunction list) : (regularExpr * ((pure * rankingfunction) option)) list = 
  print_endline ("wp4Termination"); 

  let helper ((rankingTerm, leakBehaves):rankingfunction) reIn : (pure * rankingfunction)  = 
    let (transitionSummary:transitionSummary) = transitionSummary reIn in 
    print_endline ("current ranking function is " ^ string_of_terms rankingTerm); 

    let (precondition: pure option) = List.fold_left transitionSummary ~init:None  
      ~f:(fun acc (path, stateLi) ->  
      print_endline ("transitionSummary: " ^ string_of_transitionSummary [(path, stateLi)]);

      let (pureIter:pure option) = 

        let rankingTerm' = computePostRankingFunctionFromTransitionSUmmary rankingTerm stateLi in 
        let left_hand_side = PureAnd (guard, path) in 
        let right_hand_side = Gt(normalise_terms (Minus(rankingTerm, rankingTerm')), Basic(BINT 0))in
        if entailConstrains left_hand_side FALSE then 
          (
          (*
          print_endline ("guard: " ^ string_of_pure guard); 
          print_endline ("path: " ^ string_of_pure path);   
          print_endline ("false left_hand_side: " ^ string_of_pure left_hand_side ^ " => " ^ string_of_pure right_hand_side); 
          *)
    
          Some FALSE ) 
        else 
          (
          (*print_endline ("entailConstrains: " ^ string_of_pure left_hand_side ^ " => " ^ string_of_pure right_hand_side); *)
    
          if containUnknown rankingTerm' then Some FALSE 
          else 
            if entailConstrains left_hand_side right_hand_side then None 
            else Some right_hand_side)
      in 

      match acc, pureIter with 
      | Some a, None 
      | None, Some a -> Some a 
      | None , None -> None 
      | Some a, Some b -> Some (PureAnd(a, b))
    ) 
    in 
    match precondition with 
    | None -> 
      print_endline("wp4Termination " ^ string_of_pure (TRUE)); 
      TRUE, (rankingTerm, leakBehaves) 
    | Some pre -> 
      if entailConstrains pre FALSE then FALSE, (rankingTerm, leakBehaves) 
      else pre, (rankingTerm, leakBehaves)
  in 

  (* for each path, it is enough that one ranking function is be decresing, so disjunct on the results *)
  let rec aux (rankingTermLi:rankingfunction list) reIn : (regularExpr * ((pure * rankingfunction) option)) list = 
    match rankingTermLi with 
    | [] -> [(reIn , None)] (* there is no ranking function make this trace terminate *)
    | rankingTerm :: tail -> 
      (match helper rankingTerm reIn  with 
      | FALSE, _ -> aux tail reIn
      | cond, rf -> [(reIn , Some (cond, rf))]
      )

  in 

  (* for each path, we need to try at least one ranking function should be decresing, so conjucntion on the results *)
  let rec iterator reLi (rankingTermLi:rankingfunction list) : (regularExpr * ((pure * rankingfunction) option)) list = 
    match reLi with 
    | [] -> [] 
    | [re] ->  aux rankingTermLi re
    | re::rest -> 
      let p1 = aux rankingTermLi re in 
      let p2 = iterator rest rankingTermLi in 
      p1 @ p2 
      (*normalise_pure (PureAnd (p1, p2)) *)
      
  in 

  match rankingFuns with 
  | [] -> [(re, None)]
  | rankingTermLi -> 
    let (reLi:regularExpr list) = decomposeRE re in 
    iterator reLi rankingTermLi

    


let rec fstEleList2regularExpr (record:fstElem list) : regularExpr  =
  match  record with 
  | [] -> Emp 
  | [x] -> eventToRe x
  | x::xs -> Concate (eventToRe x, fstEleList2regularExpr xs)

let rec getLast (record:fstElem list) : (fstElem list * fstElem ) option  =
  match record with 
  | [] -> None 
  | [x] -> Some ([], x) 
  | x :: xs  -> 
    (match getLast xs with
    | None -> None 
    | Some (hd, tail) -> Some (x::hd, tail)
    )

  
let stateAfterTerminate pi = 
      let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
      Singleton(pi, !allTheUniqueIDs) 
   


let infiniteLoopSummaryCalculus (guards:(pure*state) list ) (invariants: (pure*state) list) (re:regularExpr) =  
  let (frameGuard:regularExpr) = List.fold_left guards ~init:Emp ~f:(fun acc a -> Concate (acc, Guard a)) in 
  let (frameState:regularExpr) = List.fold_left (invariants) ~init:frameGuard ~f:(fun acc a -> Concate (acc, Singleton a)) in 


  let pathConditions = getAllPathConditions re in 
  let (decomposedPathConditions:pure list) = removeRedundant (flattenList (List.map ~f:(fun p -> decomposePure p ) (pathConditions) )) comparePure in 
  let (predNames:string list) = List.fold_left decomposedPathConditions ~init:[] 
      ~f:(fun acc a -> 
        match a with 
        | Predicate(str, _) -> acc @ [str] 
        | _ -> acc) 
  in
  if not (twoStringSetOverlap predNames [evenKeyWord; oddKeyWord])  then  Omega (frameState) (*Omega (Concate(frameState, re)) *)
  else 


  let rec reoccur (his:fstElem list)  f =     
    match his with 
    | [] -> false 
    | hd::tail -> 
      
      let temp = relaxed_compareEvent hd f in 
      (*print_endline ("comparing " ^ string_of_fst_event hd ^ " and " ^ string_of_fst_event f);
      print_endline (string_of_bool temp); 
      *)
      if temp then true else  reoccur tail f 
      
  in 
  let rec helper (reIn:regularExpr) (his:fstElem list) : (fstElem list) list = 
    print_endline ("his: " ^ string_of_regularExpr (fstEleList2regularExpr his));

    let (fstSet:(fstElem list)) = fst reIn in 
    if List.length fstSet == 0 && List.length his == 0 then [his]
    else 
    let fstSet, reIn, his =
      if List.length fstSet == 0 then 
        match getLast his with 
        | None -> raise (Failure "getLast his error ")
        | Some (prefix, l) -> [l], re, prefix
      else fstSet, reIn, his
    in 
      flattenList(List.map ~f:(fun f -> 
        if reoccur his f then [his] 
        else 
          (print_endline ("f: " ^ string_of_fst_event (f));
          print_endline ("reIn: " ^ string_of_regularExpr (reIn));

          let deriv = normalise_es (derivitives_2 f reIn) in 
          let f' = 
            match f with 
            | GuardEv (p, loc) -> PureEv (p, loc) 
            | PureEv (p, loc) -> 
              (match p with 
              | Eq(Basic (BSTR v1), Minus (Basic (BSTR v2), Basic (BINT 1))) 
              | Eq(Basic (BSTR v1), Plus (Basic (BSTR v2), Basic (BINT 1))) -> 
                if String.compare v1 v2 == 0 
                then 
                  let revserHis = List.rev his in 
                  if reoccur revserHis (PureEv (Predicate(evenKeyWord, [Basic (BSTR v1)]), loc)) 
                  then (PureEv (Predicate(oddKeyWord, [Basic (BSTR v1)]), loc))
                  else (PureEv (Predicate(evenKeyWord, [Basic (BSTR v1)]), loc))
                else PureEv (p, loc) 
              | _ -> PureEv (p, loc) 
              )
            
            
            | _ -> raise (Failure "loop summary with a nested loop")

          in 
          let his' = his@([f']) in 
          helper deriv his' ) 

      ) fstSet)

  in 
  let (pathes: (fstElem list) list) =  helper re [] in 
  let (res:regularExpr list) = List.map ~f:(fun a -> 
    let temp =  (fstEleList2regularExpr a) in 
    let temp', _ = instantiateREStatesWithFreshNum temp [] in 
    Omega temp' 
    
    ) pathes in 
  disjunctRE res
  

let terminatingFinalState (rankingFun:rankingfunction list) persistant (reFalse:regularExpr) (reInfinite): regularExpr = 
  match rankingFun with 
  | [] -> raise (Failure "wp4Termination true but no rankingFun")
  | (rf, None)::_ -> 
    let finalState = normalise_pure_prime (Eq(rf, Basic(BINT 0))) in 
    let ev = stateAfterTerminate finalState in 
    Concate (Concate (ev, persistant), reFalse)
  | (rf, Some re)::_ -> 

    let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
    let gT =  (Gt(rf, Basic(BINT 0) ), !allTheUniqueIDs) in 
    let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
    let gNT =  (LtEq(rf, Basic(BINT 0) ), !allTheUniqueIDs) in

    let finalState = normalise_pure_prime (Eq(rf, Basic(BINT 0))) in 
    let ev = stateAfterTerminate finalState in 

    let terminaing = Concate (Guard(gT), Concate (Concate (ev, persistant), re)) in
    let nonterminaing = Concate (Guard(gNT), reInfinite) in
    Disjunction(terminaing, nonterminaing)

let leakingPath_break_return (weakestPre:pure) (rankingFuns:regularExpr) : regularExpr option = 
  let negatedWPC = 
    match weakestPre with
    | Gt(t1, t2) | Lt(t1, t2) -> Eq(t1, t2)
    | _ -> normalise_pure(Neg weakestPre) in 
  let rankingFuns = decomposeRE rankingFuns in 
  
  let rec helper (rankingFunsIn:regularExpr list) = 
    match rankingFunsIn with 
    | [] -> None 
    | leaking :: xs  -> 
      
      let (pathConditions:pure list) = getAllPathConditions leaking in 
       
      print_endline("negatedWPC: " ^ string_of_pure negatedWPC);
      print_endline(string_of_regularExpr leaking);
      print_endline ("leakingPath_break_return\n" ^ (String.concat ~sep:",\n" (List.map ~f:(fun p -> string_of_pure p) (pathConditions))));   

      if existAux comparePure pathConditions negatedWPC then Some leaking 
      else helper xs


  in helper rankingFuns
    


let getLoopSummary (re:regularExpr) (path:pure) (reNonCycle:regularExpr): regularExpr =  
  let re = normalise_es re in
  print_endline ("getLoopSummary path:" ^ string_of_pure path) ;

  (*
  print_endline ("reFalse:" ^ string_of_regularExpr reNonCycle) ;
  print_endline ("loop body:\n" ^ string_of_regularExpr (re));
  *)
  let (fstSet:(fstElem list)) = removeRedundant (fst re) compareEvent in 
  let pi, rankingFuns, leakingBranches, nonleakingBranches =  
    (match fstSet with 
    | [GuardEv (pi, loc)] ->  
      let f = GuardEv (pi, loc) in 
      let deriv = normalise_es (derivitives f re) in 
      let leakingBranches, nonleakingBranches = devideByExitOrReturn deriv in 

      (*
      print_endline ("leakingBranches: " ^ string_of_regularExpr leakingBranches) ; 
      print_endline ("nonleakingBranches: "  ^ string_of_regularExpr nonleakingBranches) ; 
    *)
      let (rankingFuns:rankingfunction list ) = makeAGuess pi leakingBranches in 
      let rankingFuns = removeRedundant rankingFuns (fun (a, _) (b , _) -> stricTcompareTerm a b ) in 
      pi, rankingFuns, leakingBranches, nonleakingBranches

    | [PureEv (_, _)] -> raise (Failure "loop starting with PureEv") 
    | _-> raise (Failure "loop starting with more than one fst")
    )
  in 


  (*
  print_endline ("\nRankingFuns \n" ^ (String.concat ~sep:",\n" (List.map ~f:(fun (p, re) -> string_of_ranking_function (p, re)) (rankingFuns))));   
  print_endline ("loop guard: " ^ string_of_pure pi );
  *)


                                            (* a trace,    Some(terminational wp, ranking function) *)
  let (analyseEachTraceEachRankingFunction:(regularExpr * ((pure * rankingfunction) option)) list) = wp4Termination nonleakingBranches (PureAnd(pi, path)) rankingFuns in 

  let temp = List.map analyseEachTraceEachRankingFunction ~f:(fun (reIn, res) -> 
    let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
    let loopGuard = (pi, !allTheUniqueIDs) in 

    match res with 
    | None -> (* there exist no ranking function which decearces *)

      let invariants = List.fold_left rankingFuns ~init:[loopGuard ] 
        ~f:(fun acc (rf, _) -> 
        let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
        let ntGuard =  (normalise_pure_prime (Gt(rf, Basic(BINT 0))), !allTheUniqueIDs) in 
        acc@[(ntGuard)]) in 

      let (pathConditions:pure list) = getAllPathConditions reIn in 

      let (omegaGuard: (pure * state) list), omegaGuardSimple = 
        let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
        match pathConditions with 
        | [] -> [(Ast_utility.TRUE, !allTheUniqueIDs)], Ast_utility.TRUE
        | p::_ -> [(p, !allTheUniqueIDs)], p
      in 

      let stateWhenNonTerminate_fixpoint = 
        if entailConstrains (PureAnd(path, omegaGuardSimple)) FALSE then Bot 
        else 
        infiniteLoopSummaryCalculus (loopGuard :: omegaGuard) invariants reIn in 
      print_endline ("!!! " ^ string_of_regularExpr reIn ^ " has no decreasing argument !");
      print_endline ("stateWhenNonTerminate_fixpoint " ^ string_of_regularExpr stateWhenNonTerminate_fixpoint);

      (stateWhenNonTerminate_fixpoint)


    | Some (weakestPre, (rfterm, leakingRE)) -> (* there exist a ranking function, and a termination segement leakingRE *)
      (*print_endline("wp4Termination weakestPre raw: " ^ string_of_pure (weakestPre));  *)
      let rf = (rfterm, leakingRE) in 
      let weakestPre = normalise_pure_prime (weakestPre) in 
      let startingState =  normalise_pure_prime (Gt(rfterm, Basic(BINT 0))) in 

      let weakestPre, leakingRE = 
        match leakingPath_break_return weakestPre leakingBranches with
        | None -> weakestPre, leakingRE
        | Some leakingRE -> Ast_utility.TRUE, Some leakingRE
      in 


      print_endline ("!!! " ^ string_of_regularExpr reIn ^ " terminates with ranking function " ^ string_of_ranking_function rf ^ " when " ^ string_of_pure weakestPre ^ " and "^ string_of_pure startingState);


      (*
      1.   weakestPre = true, temrinating 
      2.   weakestPre = false, non-terminating 
      3.   (1 \/ 2) . reFalse 
      *)

      let (persistant:regularExpr) = normalise_es (getPersistantValuation reIn) in 


      let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
      let terminatingGuard = Guard (weakestPre, !allTheUniqueIDs) in 
      let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
      let terminatingGuardWRTRF = Guard (startingState, !allTheUniqueIDs) in 

      let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
      let terminatingFinalState = Singleton (Eq(rfterm, Basic(BINT 0)), !allTheUniqueIDs) in 
      let terminatingRE1 = Concate (Guard loopGuard, Concate(terminatingGuard, Concate(terminatingGuardWRTRF, terminatingFinalState))) in 
      let leakingBehave = match leakingRE with | Some leakingRE -> leakingRE | None -> Emp in 
      let terminatingRE2 = Concate (terminatingRE1, Concate(leakingBehave, persistant)) in 

        
    

      let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
      let nonTerminatingGuard = (normalise_pure_prime(Neg weakestPre), !allTheUniqueIDs) in 
      let non_terminating_fixpoint = infiniteLoopSummaryCalculus ([nonTerminatingGuard]) [loopGuard; nonTerminatingGuard] reIn in 
      let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
      let nonTerminatingGuardWRTRF = (normalise_pure_prime(Neg startingState), !allTheUniqueIDs) in 
      let non_terminating_fixpointWRTRF = 
        if entailConstrains (PureAnd(pi, Neg startingState)) FALSE then Bot 
        else 
        infiniteLoopSummaryCalculus ([nonTerminatingGuardWRTRF]) [loopGuard; nonTerminatingGuardWRTRF] reIn in 

      print_endline ("disj 1 = " ^ string_of_regularExpr (Concate (terminatingRE2, reNonCycle)));
      print_endline ("disj 2 = " ^ string_of_regularExpr (non_terminating_fixpoint ));

      disjunctRE [Concate (terminatingRE2, reNonCycle); non_terminating_fixpoint(*; non_terminating_fixpointWRTRF *)]
  )
  in 
  disjunctRE temp 




let rec containCycle re : bool = 
  match re with 
  | Disjunction (re1, re2)
  | Concate (re1, re2) -> containCycle re1 || containCycle re2 
  | Kleene _ -> true 
  | _ -> false 

  
let rec convertAllTheKleeneToOmega (re:regularExpr) (path:pure): regularExpr * pure = 
  match re with 
  
  | Disjunction(rFalse, Kleene (reIn)) 
  | Disjunction(Kleene (reIn), rFalse) -> 
    let reIn =
      if containCycle reIn then 
        let reIn', _ = convertAllTheKleeneToOmega reIn path in 
        reIn'
      else reIn
    in 


    let reNonCycle, path1 = convertAllTheKleeneToOmega rFalse path in 
    let reNonCycle = normalise_es reNonCycle in 
    print_endline ("reNonCycle: " ^ string_of_regularExpr  reNonCycle);

    
    let fst = fst reNonCycle in 
    let reNonCycle'  = 
      match fst with 
      | [(GuardEv gv)] -> normalise_es (derivitives (GuardEv gv) reNonCycle)
      | _  -> raise (Failure "reNonCycle does not start with a GuardEv")
      (* | [] -> reNonCycle *)
    in 
    let re2, path2 =  
      let loopsummary = normalise_es (getLoopSummary reIn (normalise_pure path) reNonCycle') in  
      print_endline ("loopsummary1: " ^ string_of_regularExpr  loopsummary);
      loopsummary, path
    in 
    Disjunction(reNonCycle, re2), PureOr(path1, path2)

  | Kleene reIn -> (print_endline  "convertAllTheKleeneToOmega not possible"); 
    let reIn =
      if containCycle reIn then 
        let reIn', _ = convertAllTheKleeneToOmega reIn path in 
        reIn'
      else reIn
    in 

    (*let normalForm = normaliseTheDisjunctions (deleteAllTheJoinNodes reIn) in *)
    let loopsummary = getLoopSummary reIn (normalise_pure path) Emp in  
    print_endline ("loopsummary2: " ^ string_of_regularExpr  loopsummary);
    loopsummary, path
    
  
  | Disjunction(r1, r2) -> 
    let re1, path1 = convertAllTheKleeneToOmega r1 path in 
    let re2, path2 = convertAllTheKleeneToOmega r2 path in 
    Disjunction(re1, re2), PureOr(path1, path2)
  | Concate (r1, r2) -> 
    let re', path' = convertAllTheKleeneToOmega r1 path in 
    let re2', path'' = convertAllTheKleeneToOmega r2 path' in 
    Concate(re',  re2'), path''
  | Guard (pi', _) -> re, PureAnd(pi', path)
  | _ -> re, path

  ;;

let rec recordTheMaxValue4RE (re:regularExpr): unit = 
  match  re with 
  | Guard (_, loc)
  | Singleton (_, loc) -> if loc > !allTheUniqueIDs then allTheUniqueIDs:=loc else ()
  | Concate (re1, re2) 
  | Disjunction (re1, re2) -> recordTheMaxValue4RE re1; recordTheMaxValue4RE re2
  | Omega reIn | Kleene (reIn) -> recordTheMaxValue4RE reIn 
  | Bot | Emp -> ()


let rec mapToOddEvenDomain (re:regularExpr): regularExpr =
  match  re with 
  | Singleton (Eq (Basic(BSTR var), Minus(Basic(BSTR var1),Basic(BINT 1) )), loc) -> 
    if String.compare var var1 == 0 then 
      let re1 = Concate (Guard(Predicate(evenKeyWord, [Basic(BSTR var)]), loc) , Singleton(Predicate(oddKeyWord, [Basic(BSTR var)]), loc)) in 
      let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
      let re2 = Concate (Guard(Predicate(oddKeyWord, [Basic(BSTR var)]), !allTheUniqueIDs) , Singleton(Predicate(evenKeyWord, [Basic(BSTR var)]), !allTheUniqueIDs)) in 
      Disjunction(re1, re2)
    else re

  | Concate (re1, re2) ->  Concate (mapToOddEvenDomain re1, mapToOddEvenDomain re2) 
  | Disjunction (re1, re2) -> Disjunction (mapToOddEvenDomain re1, mapToOddEvenDomain re2)
  | Omega reIn -> Omega (mapToOddEvenDomain reIn )
  | Kleene (reIn) -> Kleene (mapToOddEvenDomain reIn )
  | _ -> re



let getAllImplicationLeft (ctls:ctl list): pure list = 
  List.fold_left ~init:[] ~f:(fun acc ctl -> acc @ getAllPureFromImplicationLeft  ctl) ctls 


let computeSummaryFromCGF (procedure:Procdesc.t) (specs:ctl list) : regularExpr = 

  let pass =  normalise_es (getRegularExprFromCFG procedure) in 
  
  print_endline ("\nAfter getRegularExprFromCFG:\n"^string_of_regularExpr (pass)^ "\n------------"); 

  let pass, _ = convertAllTheKleeneToOmega pass (Ast_utility.TRUE) in 
  let pass = normalise_es (pass) in  (*this is the step for sumarrizing the loop*)

  print_endline ("\nAfter convertAllTheKleeneToOmega:\n"^string_of_regularExpr (pass)^ "\n------------"); 

  let pass, _ = instantiateREStatesWithFreshNum (pass) [] in  (*this is the step for renaming the states *)
  let pass, _ = deletePossibleGuards (pass) [] in  
  let pass = normalise_es (pass) in  (*this is the step for sumarrizing the loop*)


  print_endline ("\nAfter renaming and deletePossibleGuards:\n"^string_of_regularExpr (pass)^ "\n------------"); 

  (*

  print_endline ("\nPASS4':\n"^string_of_regularExpr (pass)^ "\n------------"); 
  let pass, _ = instantiateREStatesWithFreshNum (pass) [] in  (*this is the step for renaming the states *)
  let pass = normalise_es_prime pass in 
  print_endline ("\nPASS6:\n"^string_of_regularExpr (pass)^ "\n------------"); 
*)
  

  (*
  let (pathConditionsSpecOnTheLeft:pure list) = getAllImplicationLeft specs in 
  
  print_endline ("pathConditionsSpecOnTheLeft \n" ^ (String.concat ~sep:",\n" (List.map ~f:(fun p -> string_of_pure p) (pathConditionsSpecOnTheLeft))));   
 *)


  pass
  ;;


let rec findRelaventValueSetFromTerms (t:terms) (var:string) : int list = 
  match t with 
  | Basic (BINT n) -> [n](*[n+1 ; n; n-1]*)
  | Plus (t1, t2) 
  | Minus (t1, t2) -> findRelaventValueSetFromTerms t1 var @ findRelaventValueSetFromTerms t2 var 
  | _ -> []

let rec findRelaventValueSetFromPure (p:pure) (var:string) : int list = 
  match p with 
  | Eq (Basic (BSTR s), t2) 
  | Gt (Basic (BSTR s), t2)  
  | LtEq (Basic (BSTR s), t2) ->  
    if String.compare s var == 0 then 
      let seeds = findRelaventValueSetFromTerms t2 var in 
      List.fold_left seeds ~init:[] ~f:(fun acc n -> acc @ [n; n+1])
      else [] 
  | GtEq (Basic (BSTR s), t2) 
  | Lt (Basic (BSTR s), t2) ->
    if String.compare s var == 0 then 
      let seeds = findRelaventValueSetFromTerms t2 var in 
      List.fold_left seeds ~init:[] ~f:(fun acc n -> acc @ [n; n-1])
      else [] 
  | PureOr (p1, p2)
  | PureAnd (p1, p2) -> findRelaventValueSetFromPure p1 var @ findRelaventValueSetFromPure p2 var 
  | Neg pIn -> findRelaventValueSetFromPure pIn var 
  | _ -> [] 

let rec findRelaventValueSet (re:regularExpr) (var:string) : int list = 
  match re with 
  | Emp | Bot -> [] 
  | Singleton (p, _) | Guard(p, _) -> findRelaventValueSetFromPure p var 
  | Disjunction(r1, r2) 
  | Concate (r1, r2) -> findRelaventValueSet r1 var @ findRelaventValueSet r2 var 
  | Omega (reIn) | Kleene (reIn) -> findRelaventValueSet reIn var
  ;;





let getAllPathConditionsCTL (ctls:ctl list): pure list = 
  List.fold_left ~init:[] ~f:(fun acc ctl -> acc @ getAllPureFromCTL ctl) ctls 

  


let rec getUnknownVars (re:regularExpr): string list = 
  match re with 
  | Singleton (Eq (Basic(BSTR var), Basic ANY), _)  -> [var]
  | Concate(re1, re2) 
  | Disjunction (re1, re2) -> getUnknownVars re1 @ getUnknownVars re2
  | Omega re -> getUnknownVars re 
  | Kleene _ -> raise (Failure "not possible getUnknownVars kleene")
  | Emp | Bot | Guard _  | _ -> []



let rec getRelaventPure (p:pure) (str:string) : pure option = 
  match p with 
  | TRUE | FALSE | Predicate _ -> None   
  | Gt (t1, Basic(BINT _)) 
  | Lt (t1, Basic(BINT _)) 
  | GtEq (t1, Basic(BINT _)) 
  | LtEq (t1, Basic(BINT _)) 
  | Eq (t1, Basic(BINT _)) -> 
    let getVarT1 = getAllVarFromTerm t1 [] in 
    if existAux (fun a b -> String.compare a b == 0) getVarT1 str 
    then Some p else None  
  
  | PureOr (p1, p2) ->
    (match (getRelaventPure p1 str, getRelaventPure p2 str) with 
    | None, None -> None 
    | Some p1', Some p2' -> Some (PureOr(p1', p2')) 
    | Some p1', None -> Some p1' 
    | None , Some p2' -> Some p2' 
    )
  | PureAnd (p1, p2) ->
    (match (getRelaventPure p1 str, getRelaventPure p2 str) with 
    | None, None -> None 
    | Some p1', Some p2' -> Some (PureAnd(p1', p2')) 
    | Some p1', None -> Some p1' 
    | None , Some p2' -> Some p2' 
    )
  | Neg pIn -> 
    (match getRelaventPure pIn str with 
    | None -> None 
    | Some _ -> Some p 
    )
  | _ -> None 


let rec convertSTR2VARTerms (t:terms) : terms = 
  match t with 
  | Basic (BSTR str) ->  Basic (BSTR str)
  | Minus (t1, t2) -> Minus (convertSTR2VARTerms t1, convertSTR2VARTerms t2) 
  | Plus (t1, t2) -> Plus (convertSTR2VARTerms t1, convertSTR2VARTerms t2) 
  | _ -> t 

let rec convertSTR2VAR (pi:pure) : pure = 
  match pi with
  | Eq (t1, t2) ->  Eq (convertSTR2VARTerms t1, convertSTR2VARTerms t2)
  | Gt (t1, t2)  ->  Gt (convertSTR2VARTerms t1, convertSTR2VARTerms t2)
  | Lt (t1, t2) ->  Lt (convertSTR2VARTerms t1, convertSTR2VARTerms t2)
  | GtEq (t1, t2) ->  GtEq (convertSTR2VARTerms t1, convertSTR2VARTerms t2)
  | LtEq (t1, t2) ->  LtEq (convertSTR2VARTerms t1, convertSTR2VARTerms t2)
  | Neg p -> Neg (convertSTR2VAR p)
  | PureAnd (pi1, pi2) -> PureAnd (convertSTR2VAR pi1, convertSTR2VAR pi2)
  | PureOr (pi1,pi2) -> PureOr (convertSTR2VAR pi1, convertSTR2VAR pi2)
  | Predicate (str, terms) -> Predicate (str, List.map terms ~f:convertSTR2VARTerms)
  | _ -> pi


  ;;

let rec pathConditionRelatedToVar str (pathConditions:pure list): pure list = 
  List.fold_left pathConditions ~init:[] ~f:(fun acc p -> 
    match getRelaventPure p str with 
    | None  -> acc 
    | Some p' -> acc @ [p'] 
  )


let rec updateCurrentValuation (currentValuation: (string * basic_type) list) (var:string) (n:basic_type): (string * basic_type) list = 
  match currentValuation with 
  | [] -> [(var, n) ]
  | (var1, n1) :: xs  -> 
    if String.compare var var1 ==0 then (var, n) :: xs 
    else (var1, n1) :: updateCurrentValuation xs var n 

let rec findCurrentValuation (currentValuation: (string * basic_type) list) (var:string) : int option = 
  match currentValuation with 
  | [] -> None 
  | (var1, (BINT n)) :: xs  -> 
    if String.compare var var1 ==0 then Some n
    else findCurrentValuation xs var
  | _::xs -> findCurrentValuation xs var

let rec pureOfCurrentState (currentValuation: (string * basic_type) list) : pure = 
  match currentValuation with 
  | [] -> TRUE 
  | (var, n):: xs-> PureAnd(Eq(Basic (BSTR var), Basic n), pureOfCurrentState xs) 

let rec pureOfPathConstrints (currentValuation: (pure) list) : pure = 
  match currentValuation with 
  | [] -> TRUE 
  | p:: xs-> PureAnd(p, pureOfPathConstrints xs) 

  
let rec findrelationFromPredicatesSpec (predicatesSpec:pure list) (str:string) (loc:terms): relation list = 

  match predicatesSpec with 
  | [] -> [] 
  | p :: xs  -> 
    (match p with 
    | Eq (Basic( BSTR v1), Basic( BSTR v2)) -> 
      if String.compare v1 str == 0 || String.compare v2 str == 0 then 
      [(assignKeyWordVar, [Basic( BSTR v1) ; loc ; Basic( BSTR v2)])]
      else findrelationFromPredicatesSpec xs str loc
    | Eq (Basic( BSTR v1), Basic( BINT v2)) -> 
      if String.compare v1 str == 0  then 
      [(assignKeyWord, [Basic( BSTR v1) ; loc ; Basic( BINT v2)])]
      else findrelationFromPredicatesSpec xs str loc

    | Neg (Eq (Basic( BSTR v1), Basic( BSTR v2)) )-> 
      if String.compare v1 str == 0 || String.compare v2 str == 0 then 
      [(notEQKeyWordVar, [Basic( BSTR v1) ; loc ; Basic( BSTR v2)])]
      else findrelationFromPredicatesSpec xs str loc
    | Neg (Eq (Basic( BSTR v1), Basic( BINT v2))) -> 
      if String.compare v1 str == 0  then 
      [(notEQKeyWord, [Basic( BSTR v1) ; loc ; Basic( BINT v2)])]
      else findrelationFromPredicatesSpec xs str loc


    | Gt (Basic( BSTR v1), Basic( BSTR v2)) 
    | LtEq (Basic( BSTR v1), Basic( BSTR v2)) -> 
      if String.compare v1 str == 0 || String.compare v2 str == 0 then 
      [(leqKeyWordVar, [Basic( BSTR v1) ; loc ; Basic( BSTR v2)]);
       (gtKeyWordVar, [Basic( BSTR v1) ; loc ; Basic( BSTR v2)])]
      else findrelationFromPredicatesSpec xs str loc

    | Gt (Basic( BSTR v1), Basic( BINT v2)) 
    | LtEq (Basic( BSTR v1), Basic( BINT v2)) -> 
      if String.compare v1 str == 0  then 
      [(leqKeyWord, [Basic( BSTR v1) ; loc ; Basic( BINT v2)]);
      (gtKeyWord, [Basic( BSTR v1) ; loc ; Basic( BINT v2)])]
      else findrelationFromPredicatesSpec xs str loc



    | Lt (Basic( BSTR v1), Basic( BSTR v2)) 
    | GtEq (Basic( BSTR v1), Basic( BSTR v2)) -> 
      if String.compare v1 str == 0 || String.compare v2 str == 0 then 
      [(geqKeyWordVar, [Basic( BSTR v1) ; loc ; Basic( BSTR v2)]);
      (ltKeyWordVar, [Basic( BSTR v1) ; loc ; Basic( BSTR v2)])]
      else findrelationFromPredicatesSpec xs str loc

    | Lt (Basic( BSTR v1), Basic( BINT v2)) 
    | GtEq (Basic( BSTR v1), Basic( BINT v2)) -> 
      if String.compare v1 str == 0  then 
      [(geqKeyWord, [Basic( BSTR v1) ; loc ; Basic( BINT v2)]);
      (ltKeyWord, [Basic( BSTR v1) ; loc ; Basic( BINT v2)])]
      else findrelationFromPredicatesSpec xs str loc


    | _ -> findrelationFromPredicatesSpec xs str loc
    )

(* predicates are the precicates derived from the program, whereas the 
   predicatesSpec are the precicates derived from the specifiction, 
   the difference is that precicates needs to be sampled at the start location, 
   where as predicatesSpec only matters to generate facts for PureEv
*)
let rec getFactFromPureEv (p:pure) (state:int) (predicates:pure list) (predicatesSpec:pure list) (pathConstrint: (pure list)) (currentValuation: (string * basic_type) list): (((string * basic_type) list) * relation list)= 
  (*
  print_endline ("predicates getFactFromPureEv \n" ^ (String.concat ~sep:",\n" (List.map ~f:(fun p -> string_of_pure p) (predicates))));   
 *)
  (*print_endline ("\n======\npredicates pure \n" ^ string_of_pure p); 
*)
  let relevent (conds:pure) (var: string) : bool = 
    let (allVar:string list) = getAllVarFromPure conds [] in 
    (twoStringSetOverlap allVar ([var]))
  in 

  let rec removeConstrint (pLi:(pure list)) (var:string) : pure = 
    match pLi with 
    | [] -> TRUE 
    | p1::xs -> 
      let (allVar:string list) = getAllVarFromPure p1 [] in 
      if twoStringSetOverlap allVar [var] then removeConstrint xs var 
      else PureAnd (p1, (removeConstrint xs var ))

  in 
  let loc = Basic(BINT state) in 
  match p with 
  | Eq (Basic(BSTR str), Basic (ANY)) ->
    print_endline (str ^ " = *" );
    print_endline ("findrelationFromPredicatesSpec \n" ^ (String.concat ~sep:",\n" (List.map ~f:(fun p -> string_of_pure p) (predicates@predicatesSpec))));   

    let rel = findrelationFromPredicatesSpec (predicates@predicatesSpec) str loc in 
    currentValuation, rel

  | Gt (Basic(BSTR var), Basic t1) | LtEq (Basic(BSTR var), Basic t1) | Lt (Basic(BSTR var), Basic t1) | GtEq (Basic(BSTR var), Basic t1) | Neg (Eq (Basic(BSTR var), Basic t1) ) -> 
    (*print_endline (string_of_pure p ^ "newly added "); *)
    let currentValuation' = currentValuation in 
    (*print_endline (List.fold_left ~init:"currentValuation' " ~f:(fun acc (var, value) -> acc ^ (", " ^ var ^"=" ^ string_of_basic_t value)) currentValuation'); 
*)
    let pureOfCurrentState = pureOfCurrentState currentValuation' in 
    let pathConstrint' = removeConstrint pathConstrint var in 
    let currentConstraint = normalise_pure (PureAnd(pureOfCurrentState, pathConstrint')) in 
    (*print_endline ("currentConstraint: " ^ string_of_pure currentConstraint);
    *)
    
    let predicates' = 
        if entailConstrains currentConstraint FALSE 
        (* this is because sometimes the actual valuation of the state and the path constaint conjuncs to false, in that case, we only keep the structure *)
        then 
          (
          List.filter ~f:(fun ele -> 
          let ele = convertSTR2VAR ele in 
          relevent ele var && entailConstrains pureOfCurrentState ele) 
          (predicates@predicatesSpec) )
        else List.filter ~f:(fun ele -> 
            let res =  entailConstrains p ele in 
            (*print_endline ("entailConstrains: " ^ string_of_pure p  ^" => "^ string_of_pure ele  ^ ", is "^string_of_bool res); *)
            
            res
        ) (predicates@predicatesSpec) in 
    (*
    print_endline (List.fold_left ~init:"predicates': " ~f:(fun acc ( value) -> acc ^ (", " ^ string_of_pure value)) predicates'); *)
    let facts = flattenList (List.map ~f:(fun ele -> getFactFromPure ele state) predicates') in 
    (*
    print_endline (List.fold_left ~init:"facts': " ~f:(fun acc ( value) -> acc ^ (", " ^ string_of_relation value)) facts); 
    *)

    currentValuation', facts


  (* assign concret value *)
  | Eq (Basic(BSTR var), Basic t1)  -> 

    let currentValuation' = updateCurrentValuation currentValuation var t1 in 
    (*print_endline (List.fold_left ~init:"currentValuation' " ~f:(fun acc (var, value) -> acc ^ (", " ^ var ^"=" ^ string_of_basic_t value)) currentValuation'); 
*)
    let pureOfCurrentState = pureOfCurrentState currentValuation' in 
    let pathConstrint' = removeConstrint pathConstrint var in 
    let currentConstraint = normalise_pure (PureAnd(pureOfCurrentState, pathConstrint')) in 
    (*print_endline ("currentConstraint: " ^ string_of_pure currentConstraint);
    *)
    
    let predicates' = 
        if entailConstrains currentConstraint FALSE 
        (* this is because sometimes the actual valuation of the state and the path constaint conjuncs to false, in that case, we only keep the structure *)
        then List.filter ~f:(fun ele -> 
          let ele = convertSTR2VAR ele in 
          relevent ele var && entailConstrains pureOfCurrentState ele) 
          (predicates@predicatesSpec) 
        else List.filter ~f:(fun ele -> 
          let ele = convertSTR2VAR ele in 
          if relevent ele var 
          then 
            let res =  entailConstrains currentConstraint ele in 
            (*
            print_endline ("entailConstrains: " ^ string_of_pure currentConstraint  ^" => "^ string_of_pure ele  ^ ", is "^string_of_bool res);
            *)
            res
          else false 
        ) (predicates@predicatesSpec) in 
    let facts = flattenList (List.map ~f:(fun ele -> getFactFromPure ele state) predicates') in 
    currentValuation', facts

  | Predicate (s, terms) -> 
    if twoStringSetOverlap [s] [entryKeyWord] 
    then currentValuation, [(s, terms@[loc])] 
    (* @ flattenList (List.map ~f:(fun ele -> getFactFromPure ele state) predicates) *)
    else currentValuation, [(s, terms@[loc])] 
      

  | Eq (Basic(BSTR var), Plus(Basic(BSTR var1),Basic(BINT n) )) -> 
    
    
    if String.compare var var1 == 0 then 
      (
        match findCurrentValuation currentValuation var with 
        | None ->  currentValuation, []
        | Some n -> 
          let newBt = (BINT (n+1)) in 
          let currentValuation' =  updateCurrentValuation currentValuation var newBt  in 
          getFactFromPureEv (Eq (Basic(BSTR var), Basic newBt)) state predicates predicatesSpec pathConstrint currentValuation' 

      )
    else currentValuation, []
  | Eq (Basic(BSTR var), Minus(Basic(BSTR var1),Basic(BINT n) )) -> 
    
    
    if String.compare var var1 == 0 then 
      (
        match findCurrentValuation currentValuation var with 
        | None ->  
          print_endline ("findCurrentValuation none for " ^  string_of_pure p);
          currentValuation, []
        | Some n -> 
          let newBt = (BINT (n-1)) in 
          let currentValuation' =  updateCurrentValuation currentValuation var newBt  in 
          getFactFromPureEv (Eq (Basic(BSTR var), Basic newBt)) state predicates predicatesSpec pathConstrint currentValuation' 

      )
    else currentValuation, []



  | _ -> 
    print_endline (string_of_pure p ^ "is left out");
    currentValuation, []
  ;;

let rec pureToBodies (p:pure) (state:int ): body list = 
    let relations = getFactFromPure p state in 
    List.map ~f:(fun ((str, args)) -> 
      updateRuleDeclearation bodyDeclearation (str^"D");
      Pos (str^"D",args) ) relations 



let flowsForTheCycle (re:regularExpr) : relation list = 
  let fstSet = fst re in 
  let lastSet = fst (reverse re) in 
  let startingStates = getStatesFromFstEle fstSet in 
  let (getLastStates: state list) = getStatesFromFstEle lastSet in 
  flattenList (List.map getLastStates ~f:(fun l -> List.map ~f: (fun s -> 
    (flowKeyword, [Basic (BINT l); Basic (BINT s)])
  ) startingStates))
  (*@ (List.map startingStates ~f: (fun s -> 
    print_endline ("flowsForTheCycle " ^ string_of_int s ^"\n");
    (stateKeyWord, [Basic (BINT s)])))
    *)


let existExitKeyWord (pLi:ctl list): bool = 
  let (allPredicates:string list) = List.fold_left pLi ~init:[] ~f:(fun acc a -> acc @ (getAllPredicateFromCTL a)) in 
  twoStringSetOverlap [exitKeyWord] allPredicates
  
let getStartState re : int option = 
  match fst re with
  | [PureEv (_, state)] -> Some state 
  | _ ->  None 

let convertRE2Datalog (re:regularExpr) (specs:ctl list): (relation list * rule list) = 
  let (doneDelimiters:int list ref) = ref[] in 
  let pathConditions = getAllPathConditions re in 
  let (pathConditionsCTL:pure list) = getAllPathConditionsCTL specs in 
  (* decomposedPathConditions: this is to sample the constraints from the path *)
  let (decomposedPathConditions:pure list) = removeRedundant (flattenList (List.map ~f:(fun p -> decomposePure p ) (pathConditions) )) comparePure in 
  
  let (decomposedpathConditionsCTL:pure list) = removeRedundant (flattenList (List.map ~f:(fun p -> decomposePure p ) (pathConditionsCTL) )) comparePure in 
(* decomposedPathConditions are the precicates derived from the program, whereas the 
   decomposedpathConditionsCTL are the precicates derived from the specifiction, 

   print_endline ("SpecpathConditions \n" ^ (String.concat ~sep:",\n" (List.map ~f:(fun p -> string_of_pure p) (decomposedpathConditionsCTL))));   
  print_endline ("PorgPathConditions \n" ^ (String.concat ~sep:",\n" (List.map ~f:(fun p -> string_of_pure p) (decomposedPathConditions))));   
*)
  

  let rec mergeResults li (acca, accb) = 
    match li with 
    | [] -> (acca, accb) 
    | (a, b) :: xs -> mergeResults xs (acca@a, accb@b )
  in     

  (*let startState: state option = getStartState re in *)
  let rec ietrater reIn (previousState:int option) (pathConstrint: ((pure * state) list)) (currentValuation: (string * basic_type) list) : (relation list * rule list) = 
    let reIn = normalise_es reIn in 
    (*print_endline ( string_of_regularExpr reIn );    *)

    
    let fstSet = removeRedundant (fst reIn) compareEvent in 
    match fstSet with 
    | [] -> 
      (match previousState with 
      | Some previousState -> 
        let stateFact = (stateKeyWord, [Basic (BINT previousState)]) in 
        
        (* if the property is AG \phi, it connect the last state with the starting state, 
           if not, it adds a loop on the last state  *)
        let fact = (flowKeyword, [Basic (BINT previousState); Basic (BINT previousState )]) in 

        ([fact;stateFact], [])
      | _ -> ([], [])
      )
    | li -> 
      List.fold_left li ~init:([], []) ~f:(fun (reAcc, ruAcc) f -> 
        match f with 
        | Delimiter state -> 
          
          let (reAcc, ruAcc) = 
            (match previousState with 
            | Some previousState -> 
              let stateFact = (stateKeyWord, [Basic (BINT previousState)]) in 

              let fact = (flowKeyword, [Basic (BINT previousState); Basic (BINT state)]) in 
              let fact' = (controlFlowKeyword, [Basic (BINT previousState); Basic (BINT state)]) in 

              (match pathConstrint with 
              | [] -> [stateFact; fact], []
              | bodies -> [stateFact], [(fact', flattenList(List.map ~f:(fun (p, l) -> (pureToBodies p l)) bodies))]
              )
              

            | None  -> [], []
            )
          in 
          let (reAcc'', ruAcc'') = 
            if existAux (==) !doneDelimiters state then [], []
            else 
              (doneDelimiters := state:: !doneDelimiters;
              ietrater (derivitives f reIn) (Some state) [] currentValuation) in 
          
          mergeResults [(reAcc, ruAcc); (reAcc'', ruAcc'')] ([], [])


        | PureEv (p, state) -> 
          let (reAcc', ruAcc')  = 
            (match previousState with 
            | Some previousState -> 
              let fact = (flowKeyword, [Basic (BINT previousState); Basic (BINT state)]) in 
              let fact' = (controlFlowKeyword, [Basic (BINT previousState); Basic (BINT state)]) in 

              let stateFact = (stateKeyWord, [Basic (BINT previousState)]) in 
              (match pathConstrint with 
              | [] -> [stateFact; fact], []
              | bodies -> [stateFact], [(fact', flattenList(List.map ~f:(fun (p, l) -> (pureToBodies p l)) bodies))]
              )
            | None -> [], []) in 
          let currentValuation', valueFacts = getFactFromPureEv p state decomposedPathConditions decomposedpathConditionsCTL (List.map pathConstrint ~f:(fun (a, _)-> a)) currentValuation in 
          
          
          print_endline (List.fold_left ~init:"valueFacts " ~f:(fun acc value -> acc ^ (", " ^ string_of_relation value)) valueFacts); 
          

          let (derivitives:regularExpr) = 
            let original = (derivitives f reIn) in original
          in 

          let pathConstrint' = 
            match p with 
            | Predicate (s, _) -> 
              (*print_endline ("Specs are \n" ^ (String.concat ~sep:" , " (List.map ~f:(fun p -> string_of_ctl p) (specs)))); 
              print_endline ("existExitKeyWord of " ^ s ^ " is " ^ string_of_bool (existExitKeyWord specs)); 
              *)  
              (if String.compare s evenKeyWord ==0 ||  String.compare s oddKeyWord ==0 then 
                predicateDeclearation:= (s, ["Symbold";"Number"]) :: !predicateDeclearation 
              else if String.compare s retKeyword ==0 then 
                predicateDeclearation:= (s, ["Number";"Number"]) :: !predicateDeclearation 
              else if twoStringSetOverlap [s] [entryKeyWord;skipKeyword;retKeyword] then ()
              else if String.compare s exitKeyWord ==0 && existExitKeyWord specs then ()
              else 
                predicateDeclearation:=  !predicateDeclearation@ [(s, ["Number"])] ;
              );
              if String.compare s joinKeyword == 0 then [] else pathConstrint
            | _ -> pathConstrint
          in 

          let (reAcc'', ruAcc'') = ietrater derivitives (Some state) pathConstrint' currentValuation' in 
          mergeResults [(reAcc, ruAcc); (reAcc', ruAcc'); (valueFacts, []); (reAcc'', ruAcc'')] ([], [])

          
        | GuardEv (guard, state) ->  
          (*print_endline ("GuardEv " ^ string_of_pure guard ); *)
          let (reAcc', ruAcc')  = 
            (match previousState with 
            | Some previousState -> 
              (*let fact = (flowKeyword, [Basic (BINT previousState); Basic (BINT state)]) in *)
              let fact' = (controlFlowKeyword, [Basic (BINT previousState); Basic (BINT state)]) in 
              let currentGuardBody = (pureToBodies guard (previousState)) in 

              let stateFact = (stateKeyWord, [Basic (BINT previousState)]) in 
              (match pathConstrint, currentGuardBody with 
              | [], [] -> [stateFact;fact'], []
              | [], _ -> [stateFact], [(fact', currentGuardBody)]
              | bodies, _ -> [stateFact], [(fact', flattenList(List.map ~f:(fun (p, l) -> (pureToBodies p l)) bodies) @ currentGuardBody)]
              )
            | None -> [], []) 
          in 
          let (pathConstrint': ((pure * state) list)) = 
            match previousState with 
            | None -> pathConstrint
            | Some previousState -> 
              match pathConstrint, guard  with 
              | [], TRUE -> ([])
              | bodies, TRUE -> (bodies)

              | [], _ -> ([(guard, previousState)])
              | bodies, _ -> (bodies @ [(guard, previousState)])
          in 

          let (reAcc'', ruAcc'') = ietrater (derivitives f reIn) (Some state) pathConstrint' currentValuation in 
          mergeResults [(reAcc, ruAcc); (reAcc', ruAcc'); (reAcc'', ruAcc'')] ([], [])

        (* ietrater recycle previousState *)
        | KleeneEv _ ->  raise (Failure "having a kleene after the loop summarisation")
        | OmegaEv recycle -> 
            
          let (reAcc', ruAcc') = ietrater recycle previousState pathConstrint currentValuation in 
          let extraFlows = flowsForTheCycle recycle in 
          mergeResults [(reAcc, ruAcc); (reAcc', ruAcc'); (extraFlows, [])] ([], [])

      )
  in 
  ietrater re None [] [] 

let sortFacts factL : relation list  = 
  let rec helper ((left, right):(relation list * relation list)) liIn = 
    match liIn with 
    | [] ->  
      let left' = removeRedundant left 
        (fun (_, b) (_, d) -> compareTermList b d) in 
      (*print_endline ("before sort_unique: " ^ string_of_facts left);*)
      (*print_endline ("after sort_unique: " ^ string_of_facts left');*)
      let right' = removeRedundant right 
        (fun (n1, b) (n2, d) -> String.compare n1 n2 == 0 && compareTermList b d) in 

      left'@right'
    | (s, termL) :: xs -> 
      if String.compare s flowKeyword == 0 
      then helper (left@[(s, termL)], right) xs 
      else helper (left, right@[(s, termL)]) xs 
  in helper  ([], []) factL


let sortRules (ruleL : rule list) : rule list  = 
  sort_uniq (fun ((hd1, bodies1): rule) ((hd2, bodies2):rule) -> 
    if compareRelation hd1 hd2 && compareBodyList bodies1 bodies2 
    then 0 else -1 
  ) ruleL


let createNecessaryDisjunction (re:regularExpr ) (specs:ctl list) : regularExpr = 
  let (allVarSpec:pure list) = flattenList (List.map ~f:(fun ctl -> getAllPureFromCTL ctl) specs) in 
  (*
  print_endline ("allVarSpec:\n" ^ (String.concat ~sep:",\n" (List.map ~f:(fun p -> string_of_pure p) allVarSpec)));   
  *)

  let rec partitionRE reIn :  regularExpr list = 
    match reIn with 
    | Concate (re1, re2) -> partitionRE re1  @ partitionRE re2
    | _ -> [reIn]
  in 
  let segemants = partitionRE re in 

  (*print_endline ("\nsegemants:\n" ^ (String.concat ~sep:",\n" (List.map ~f:(fun p -> string_of_regularExpr p) segemants)) ^ "\n");
  *)
  let rec iteraterSegemnst reInLi : regularExpr = 
    match reInLi with 
    | Disjunction(es1, es2) :: xs -> 
      let x = Disjunction(es1, es2) in 
      let containRelevantPure = containRelevantPureRE x allVarSpec in 
      if containRelevantPure then 
        let derivitives = iteraterSegemnst xs in  
        (*print_endline ("derivitives " ^ string_of_regularExpr derivitives); *) 
        let derivitives1, _ = instantiateREStatesWithFreshNum (Concate (x, derivitives)) [] in 
        (*print_endline ("after  " ^ string_of_regularExpr derivitives1); *)

        derivitives1

      else Concate (x, iteraterSegemnst xs)
    | [x] ->  x
    | x :: xs  -> Concate (x, iteraterSegemnst xs)
    | [] -> Emp
  in 

  iteraterSegemnst segemants

  
let rec extend_spec_agaf pLi: unit = 
  (match pLi with 
  | PureAnd(_, Gt (_, Basic(BINT _)))  -> spec_agaf := gtKeyWord::!spec_agaf
  | PureAnd(_, Gt (_, Basic(BSTR _)))  -> spec_agaf := gtKeyWordVar::!spec_agaf

  | PureAnd(_, GtEq (_, Basic(BINT _)))  -> spec_agaf :=  geqKeyWord::!spec_agaf
  | PureAnd(_, GtEq (_, Basic(BSTR _)))  -> spec_agaf :=  geqKeyWordVar::!spec_agaf

  | PureAnd(_, LtEq (_, Basic(BINT _)) )  -> spec_agaf :=  leqKeyWord::!spec_agaf
  | PureAnd(_, LtEq (_, Basic(BSTR _)) )  -> spec_agaf :=  leqKeyWordVar::!spec_agaf

  | PureAnd(_, Eq (_, Basic(BINT _)) ) -> spec_agaf :=  assignKeyWord::!spec_agaf
  | PureAnd(_, Eq (_, Basic(BSTR _)) ) -> spec_agaf :=  assignKeyWordVar::!spec_agaf

  | PureAnd(_, Neg(Eq (_, Basic(BINT _)) ))  -> spec_agaf :=  notEQKeyWord::!spec_agaf
  | PureAnd(_, Neg(Eq (_, Basic(BSTR _)) ))  -> spec_agaf :=  notEQKeyWordVar::!spec_agaf

  | PureOr (Eq (_, Basic(BINT _)) , Eq (_, Basic(BSTR _))) ->  
    spec_agaf :=  assignKeyWord::!spec_agaf;
    spec_agaf :=  assignKeyWordVar::!spec_agaf

  | _ -> ()

  )


let do_source_file (translation_unit_context : CFrontend_config.translation_unit_context) ast =
  let tenv = Tenv.create () in
  CType_decl.add_predefined_types tenv ;
  init_global_state_capture () ;
  let source_file = translation_unit_context.CFrontend_config.source_file in
  let integer_type_widths = translation_unit_context.CFrontend_config.integer_type_widths in
  L.(debug Capture Verbose)
    "@\n Start building call/cfg graph for '%a'....@\n" SourceFile.pp source_file ;
  let cfg = compute_icfg translation_unit_context tenv ast in
  CAddImplicitDeallocImpl.process cfg tenv ;
  CAddImplicitGettersSetters.process cfg tenv ;
  CReplaceDynamicDispatch.process cfg ;
  L.(debug Capture Verbose) "@\n End building call/cfg graph for '%a'.@\n" SourceFile.pp source_file ;
  SourceFiles.add source_file cfg (Tenv.FileLocal tenv) (Some integer_type_widths) ;
  if Config.debug_mode then Tenv.store_debug_file_for_source source_file tenv ;

  L.(debug Capture Verbose) "@\n Start buidling facts for '%a'.@\n" SourceFile.pp source_file ;

  let (source_Address, decl_list, specifications, lines_of_code, lines_of_spec, number_of_protocol) = retrive_basic_info_from_AST ast in         
  let start = Unix.gettimeofday () in 

  print_endline ("<== Anlaysing " ^ source_Address  ^ " ==>");

  let () = allTheUniqueIDs := (-1) in 

  let () = ruleDeclearation := [] in 
  let () = bodyDeclearation := [] in 

  let () = predicateDeclearation := [] in 

  let facts = (Cfg.fold_sorted cfg ~init:[] 
  ~f:(fun facts procedure -> List.append facts (get_facts procedure) )) in

  (*print_endline (List.fold_left facts ~init:"" ~f:(fun acc a -> acc ^ "\n" ^ a )); *)

  let summaries = (Cfg.fold_sorted cfg ~init:[] 
    ~f:(fun accs procedure -> 
      print_endline ("\n//-------------\nFor procedure: " ^ Procname.to_string (Procdesc.get_proc_name procedure) ^":" );
      let summary = computeSummaryFromCGF procedure specifications in 
      List.append accs [summary] )) 
  in

  let () = 
    match specifications with 
    | [(AG (Imply (Atom(_, p), AF _)))] -> 
      
      extend_spec_agaf p 

      
      
    | _ -> () 


  in 

  let (factPrinting: string list) = flattenList (List.map summaries ~f: (fun summary -> 
      (*let summary' = createNecessaryDisjunction summary specifications in*)
      let (facts, rules) = convertRE2Datalog (summary) specifications in 
      ("/*" ^ string_of_regularExpr summary ^ "*/") :: 
      string_of_facts (sortFacts facts) :: 
      string_of_rules (sortRules rules) :: []
  )) in 
  

  
  let (specPrinting:string list) = List.map specifications ~f:(fun ctl -> "//" ^ string_of_ctl ctl) in 

  let predicateDeclearation = (sort_uniq (fun (a, _) (c, _) -> String.compare a c) !predicateDeclearation) in 

  let (datalogProgPrinting:string list) = 
    flattenList (List.map specifications 
    ~f:(fun item -> 
      let fname, program = (translation item) in 
      print_endline (string_of_ctl item);
      print_endline (".output "^ fname ^"Final(IO=stdout)\n") ; 
      [string_of_datalog program] 
      @ List.map !ruleDeclearation ~f:(fun a -> ".output " ^ a) 
      @ 
      
      [  ".output Start"; 
         ".output State";
         ".output flow";
      ]
      
      @ (List.map predicateDeclearation ~f:(fun (a, _) -> ".output " ^ a) )
      @ [".output "^ fname ^ outputShellKeyWord ^ "(IO=stdout)\n"]
      


     )) in 

  spec_agaf:= []; 
     
  let () = totol_Lines_of_Spec := !totol_Lines_of_Spec + lines_of_spec in 


  Out_channel.write_lines (source_Address ^ ".dl") 
  (factPrinting@specPrinting@datalogProgPrinting @ ["/* Other information \n"]@facts@["*/\n"] );


  let command = "souffle -F. -D. " ^ source_Address ^ ".dl" in 
  print_endline ("<==\n Runing Datalog $ " ^ command  ^ " \n==>");
  let _ = Sys.command command in 

  print_endline ("\nTotol_execution_time: " ^ string_of_float ((Unix.gettimeofday () -. start) (* *.1000. *) ) ^ " s"); 

  L.(debug Capture Verbose) "@\n End buidling facts for '%a'.@\n" SourceFile.pp source_file ;

  if
    Config.debug_mode || Config.testing_mode || Config.frontend_tests
    || Option.is_some Config.icfg_dotty_outfile
  then DotCfg.emit_frontend_cfg source_file cfg ;
  L.debug Capture Verbose "Stored on disk:@[<v>%a@]@." Cfg.pp_proc_signatures cfg ;
  ()


(*let do_source_file (translation_unit_context : CFrontend_config.translation_unit_context) ast =
  let tenv = Tenv.create () in
  CType_decl.add_predefined_types tenv ;
  init_global_state_capture () ;
  let source_file = translation_unit_context.CFrontend_config.source_file in
  let integer_type_widths = translation_unit_context.CFrontend_config.integer_type_widths in

  print_endline ("\n================ Here is Yahui's Code ================="); 


  let (source_Address, decl_list, specifications, lines_of_code, lines_of_spec, number_of_protocol) = retrive_basic_info_from_AST ast in         
  
  let () = totol_Lines_of_Spec := !totol_Lines_of_Spec + lines_of_spec in 

  let () = totol_Lines_of_Code := !totol_Lines_of_Code + lines_of_code in 
  let () = totol_specifications := List.append !totol_specifications specifications in 
  let start = Unix.gettimeofday () in 

  (*let reasoning_Res = List.map decl_list  
    ~f:(fun dec -> reason_about_declaration dec !totol_specifications source_Address) in 
  *)
  let compution_time = (Unix.gettimeofday () -. start) in 
    (* Input program has  *)
    let msg = 
      "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
      ^ "[CURRENT REPORT]:"
      ^ source_Address ^ "\n"
      ^ string_of_int ( !totol_Lines_of_Code ) ^ " lines of code; " 
      ^ string_of_int !totol_Lines_of_Spec ^ " lines of specs; for " 
      in 
  
    print_string (msg); 

  (*
  print_endline ("Totol_execution_time: " ^ string_of_float compution_time); 
  print_endline ("\n============ Here is the end of Yahui's Code ============\n" 
                 ^ "=========================================================\n" );
                 *)
                
  
  
  L.(debug Capture Verbose)
    "@\n Start building call/cfg graph for '%a'....@\n" SourceFile.pp source_file ;
  let cfg = compute_icfg translation_unit_context tenv ast in
  
  let out_c = Out_channel.create "zprint" in
  let fmt = F.formatter_of_out_channel out_c in
  Cfg.pp_proc_signatures fmt cfg; 

  print_string("<<<SYH:Finished creating icfg>>>\n");



  CAddImplicitDeallocImpl.process cfg tenv ;
  CAddImplicitGettersSetters.process cfg tenv ;
  CReplaceDynamicDispatch.process cfg ;
  L.(debug Capture Verbose) "@\n End building call/cfg graph for '%a'.@\n" SourceFile.pp source_file ;
  SourceFiles.add source_file cfg (Tenv.FileLocal tenv) (Some integer_type_widths) ;
  if Config.debug_mode then Tenv.store_debug_file_for_source source_file tenv ;
  if
    Config.debug_mode || Config.testing_mode || Config.frontend_tests
    || Option.is_some Config.icfg_dotty_outfile
  then DotCfg.emit_frontend_cfg source_file cfg ;
  L.debug Capture Verbose "Stored on disk:@[<v>%a@]@." Cfg.pp_proc_signatures cfg ;
  
  
  ()
  *)

