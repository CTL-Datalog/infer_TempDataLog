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
  | PureAnd (p1, p2) -> decomposePure p1 @ decomposePure p2 
  | Ast_utility.TRUE -> []
  | _ -> [p]



let conjunctPure (pi1:pure) (pi2:pure): pure = 
  if entailConstrains pi1 pi2 then pi1 
  else if entailConstrains pi2 pi1 then pi2
  else  
    let pi1 = normalise_pure pi1 in 
    let pi2 = normalise_pure pi2 in 
    (match pi1, pi2 with 
    | ((GtEq(Basic (BVAR var1), Basic(BINT 0))), PureAnd (pi11, LtEq(Basic (BVAR var2), Basic(BINT 0)))) -> 
      if String.compare var1 var2 == 0 then PureAnd(Eq(Basic (BVAR var1), Basic(BINT 0)), pi11)
      else PureAnd (pi1, pi2)
    | ((GtEq(Basic (BVAR var1), Basic(BINT 0))), LtEq(Basic (BVAR var2), Basic(BINT 0))) -> 
      if String.compare var1 var2 == 0 then Eq(Basic (BVAR var1), Basic(BINT 0))
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
        | Eq (Basic (BVAR var), t2) -> 

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
    | (Lt(Basic(BVAR(t1)), Basic(BVAR(t2))), Lt(Basic t3, Basic t4)) -> Some ([(t1,t3); (t2, t4)], facts)
    | (Gt(Basic(BVAR(t1)), Basic(BVAR(t2))), Gt(Basic t3, Basic t4)) -> Some ([(t1,t3); (t2, t4)], facts)
    | (GtEq(Basic(BVAR(t1)), Basic(BVAR(t2))), GtEq(Basic t3, Basic t4)) -> Some ([(t1,t3); (t2, t4)], facts)
    | (LtEq(Basic(BVAR(t1)), Basic(BVAR(t2))), LtEq(Basic t3, Basic t4)) -> Some ([(t1,t3); (t2, t4)], facts)
    | (Eq(Basic(BVAR(t1)), Basic(BVAR(t2))), Eq(Basic t3, Basic t4)) -> Some ([(t1,t3); (t2, t4)], facts)
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

let rec existStack stack t : Exp.t option = 
  match stack with 
  | [] -> None 
  | (exp, ident) :: xs  -> 
    if String.compare (Ident.to_string t)  (Ident.to_string ident) == 0 
    then Some exp
    else  existStack xs t

let rec expressionToTerm (exp:Exp.t) stack : terms  = 
  match exp with 
  | Var t -> 
    (match existStack stack t with 
    | Some (Lvar t) -> Basic (BVAR (Pvar.to_string t )) (** Pure variable: it is not an lvalue *)
    | Some exp -> Basic (BVAR (Exp.to_string exp ))
    | None  ->  Basic (BVAR (Ident.to_string t)) (** Pure variable: it is not an lvalue *)
    )
  | Lvar t -> Basic (BVAR (Pvar.to_string t))  (** The address of a program variable *)

  | Const t ->  (** Constants *)
    (match t with 
    | Cint i -> Basic (BINT (IntLit.to_int_exn i ))  (** integer constants *)
    | _ -> Basic BNULL
    )

  | UnOp (Neg, t, _) -> 
    (match expressionToTerm t stack with 
    | Basic (BINT n) -> Basic (BINT ((-1) * n))
    | _ -> Basic (BVAR ("UnOp1"))
    )
    
    (** Unary minus *)
  | UnOp _ -> Basic (BVAR ("UnOp"))

  | BinOp (MinusA _, e1, e2)
  | BinOp (MinusPI, e1, e2)
  | BinOp (MinusPP, e1, e2) -> 
    let t1 = expressionToTerm e1 stack in 
    let t2 = expressionToTerm e2 stack in 
    Minus (t1, t2)

  | BinOp (PlusA _, e1, e2)
  | BinOp (PlusPI, e1, e2) -> 
    let t1 = expressionToTerm e1 stack in 
    let t2 = expressionToTerm e2 stack in 
    Plus (t1, t2)

  | BinOp _ -> Basic (BVAR ("BinOp"))
  | Exn _ -> Basic (BVAR ("Exn"))
  | Closure _ -> Basic (BVAR ("Closure"))
  | Cast _ -> Basic (BVAR ("Cast"))
  | Lfield _ -> Basic (BVAR ("Lfield"))
  | Lindex _ -> Basic (BVAR ("Lindex"))
  | Sizeof _ -> Basic (BVAR ("Sizeof"))

let rec expressionToPure (exp:Exp.t) stack: pure option = 
  match exp with 
  | BinOp (Eq, BinOp (Mod _, e1, e2), e3) ->  
    let t1 = expressionToTerm e1 stack in 
    let t2 = expressionToTerm e2 stack in 
    let t3 = expressionToTerm e3 stack in 
    (match (t1, t2,  t3) with 
    | Basic(BVAR var ), Basic (BINT 2), Basic (BINT 0) -> Some (Predicate("Even", [Basic(BSTR var )])) 
    | Basic(BVAR var ), Basic (BINT 2), Basic (BINT 1) -> Some (Predicate("Odd", [Basic(BSTR var )])) 
    | _ -> None 
    )
  | BinOp (Ne, BinOp (Mod _, e1, e2), e3) ->  
    let t1 = expressionToTerm e1 stack in 
    let t2 = expressionToTerm e2 stack in 
    let t3 = expressionToTerm e3 stack in 
    (match (t1, t2,  t3) with 
    | Basic(BVAR var ), Basic (BINT 2), Basic (BINT 0) -> Some (Predicate("Odd", [Basic(BSTR var )])) 
    | Basic(BVAR var ), Basic (BINT 2), Basic (BINT 1) -> Some (Predicate("Even", [Basic(BSTR var )])) 
    | _ -> None 
    )


  | BinOp (bop, e1, e2) -> 

    let t1 = expressionToTerm e1 stack in 
    let t2 = expressionToTerm e2 stack in 
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
    | _ -> 
      print_endline ("expressionToPure None : " ^ Exp.to_string exp); 
      None
    )
    (*
    | LAnd  (** logical and. Does not always evaluate both operands. *)
    | LOr  (** logical or. Does not always evaluate both operands. *)  
    | PlusA of Typ.ikind option  (** arithmetic + *)
    | PlusPI  (** pointer + integer *)
    | MinusA of Typ.ikind option  (** arithmetic - *)
    | MinusPI  (** pointer - integer *)
    | MinusPP  (** pointer - pointer *)
    | Mult of Typ.ikind option  (** * *)
    | DivI  (** / for integers *)
    | DivF  (** / for floats *)
    | Mod  (** % *)
    | Shiftlt  (** shift left *)
    | Shiftrt  (** shift right *)
    | BAnd  (** bitwise and *)
    | BXor  (** exclusive-or *)
    | BOr  (** inclusive-or *)
    *)
  

  | UnOp (_, e, _) -> 
    (match expressionToPure e stack with 
    | Some p -> Some (Neg p)
    | None -> None 
    )
  | Const _ -> 
    if String.compare (Exp.to_string exp) "1" == 0 then Some TRUE
    else 
      (print_endline ("expressionToPure Const : " ^ Exp.to_string exp ); 
      None )
  (*| Var _ -> 
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
    print_endline ("expressionToPure 3 None : " ^ Exp.to_string exp ); 
    None 
  
let getPureFromFunctionCall (e_fun:Exp.t) (arg_ts:(Exp.t * Typ.t) list) ((Store s):IR.Sil.instr) stack =
  let funName = (Exp.to_string e_fun) in 
  if existAux (fun a b -> String.compare a b == 0) nonDetermineFunCall funName then 
    let exp1 = s.e1 in 
    Some (Eq (expressionToTerm exp1 stack, Basic(ANY)))
  else 
    let argumentTerms =  List.map arg_ts ~f:(fun (eA, _) -> expressionToTerm eA stack) in 
    Some (Predicate(funName, argumentTerms))



let rec getPureFromBinaryOperatorStmtInstructions (op: string) (instrs:Sil.instr list) stack : pure option = 
  (*print_endline ("getPureFromBinaryOperatorStmtInstructions: " ^ string_of_int (List.length instrs));
  *)
  if String.compare op "Assign" == 0 then 
    match instrs with 
    | Store s :: _ -> 
      (*print_endline (Exp.to_string s.e1 ^ " = " ^ Exp.to_string s.e2); *)
      let exp1 = s.e1 in 
      let exp2 = s.e2 in 
      Some (Eq (expressionToTerm exp1 stack, expressionToTerm exp2 stack))
    | Load l :: tail ->
      let stack' = (l.e, l.id):: stack in 
      getPureFromBinaryOperatorStmtInstructions "Assign" tail stack'
    | Call ((ret_id, _), e_fun, arg_ts, _, _)  :: Store s :: _ -> 
      (*print_endline (Exp.to_string e_fun) ;   *)
      getPureFromFunctionCall e_fun arg_ts (Store s) stack
    
    | _ -> None 
  else if String.compare op "SubAssign" == 0 then  
    match instrs with 
    | Store s :: _ ->  
      getPureFromBinaryOperatorStmtInstructions "Assign" instrs stack
    | Load l :: tail ->
      let stack' = (l.e, l.id):: stack in 
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
    | Basic(BSTR _ ) , Basic(BINT _ ) -> Some (Eq (t1, t2))
    | Basic(BVAR _ ) , Basic(BINT _ ) -> Some (Eq (t1, t2))
    (*
    | _ -> Some (Eq (t1, Basic ANY))  *)
    (* if it is temp=user_quota_size-quota_size, temp will be ANY *)
    | _ -> Some (Eq (t1, t2)) 

    )  
    
  | Load l :: tail ->
    let stack' = (l.e, l.id):: stack in 
    getPureFromDeclStmtInstructions tail stack'

  | Call ((ret_id, _), e_fun, arg_ts, _, _)  :: Store s :: _ -> 
    (*print_endline (Exp.to_string e_fun) ;   *)
    getPureFromFunctionCall e_fun arg_ts (Store s) stack
    
  | _ -> None

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
  | Exit_node ->  Emp(* Singleton (Predicate ("Exit", []), node_key) *), []
  | Join_node ->  Singleton(Predicate (joinKeyword, []), node_key) , []
  | Skip_node _ ->  Singleton(Predicate (skipKeyword, []), node_key) , []
  | Prune_node (f,_,_) ->  
    (match instrs with 
    | Prune (e, loc, f, _):: _ ->  
      (match expressionToPure e stack with 
      | Some p -> Guard(p, node_key)
      | None -> Guard(TRUE, node_key) ), []
    | _ -> Singleton(TRUE, node_key) , []
    )
  

  | Stmt_node stmt_kind ->         
    match stmt_kind with 
    | BinaryOperatorStmt (op) -> 
      if existAux (fun a b-> String.compare a b ==0) ["EQ";"GT";"LT";"NE";"LE";"GE"] op then 
        (*String.compare op "EQ" == 0 || String.compare op "GT" == 0 then  *)
        let stack = List.fold_left instrs ~init:[] ~f:(fun acc (ins:Sil.instr) -> 
          match ins with 
          | Load l -> (l.e, l.id) :: acc 
          | _ -> acc
        ) in 
        Emp , stack
        (*Singleton(TRUE, node_key), stack *)
        (* This is to avoid th extra (T)@loc before the guard, we only need to 
           record the stack, but no need any event *)
      else 
        (match getPureFromBinaryOperatorStmtInstructions op instrs stack with 
        | Some pure -> Singleton (pure, node_key), []
        | None -> Singleton(TRUE, node_key), [] )  
        
    | UnaryOperator 
    | DeclStmt -> 
      (match getPureFromDeclStmtInstructions instrs stack with 
      | Some pure -> Singleton (pure, node_key), []
      | None -> Singleton(TRUE, node_key), [] )
    | ReturnStmt -> 
      (match instrs with 
      | Store s :: _ -> 
        (*print_endline (Exp.to_string s.e1 ^ " = " ^ Exp.to_string s.e2); *)
        let exp2 = s.e2 in 
        predicateDeclearation:= (retKeyword, ["Number";"Number"]) :: !predicateDeclearation ;

        Singleton (Predicate (retKeyword, [expressionToTerm exp2 stack]), node_key), []
      | _ -> 
        Singleton (Predicate (retKeyword, []), node_key), []
      )
    | Call x  -> 
      (match instrs with 
      | Call ((ret_id, _), e_fun, arg_ts, _, _)  :: _ -> 
        let argumentTerms =  List.map arg_ts ~f:(fun (eA, _) -> expressionToTerm eA stack) in 
        let argumentTermsType = List.map argumentTerms ~f:(fun a -> match a with | Basic(BINT _ ) ->"Number" | Basic(BVAR _ ) -> "Symbol" | Basic(BSTR _ ) -> "Symbol" | _ -> "")  in 
        let funName = (Exp.to_string e_fun) in 
        let funName = String.sub funName 5 (String.length funName - 5) in 
        predicateDeclearation:= (funName, argumentTermsType@["Number"]) :: !predicateDeclearation ;
        Singleton (Predicate (funName, argumentTerms), node_key), [] 
       
      | _ -> Singleton (Predicate (x, []), node_key), []
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


(* the old version of producing the regular expressions *)
let rec iterateProc (env:reCFG) (currentState:Procdesc.Node.t): regularExpr = 
  let (history, stack) = env in 
  let node_key = getNodeID currentState in
  match existRecord history node_key with 
  | Some (prefix, cycle) -> 
    let prefix', stack' = recordToRegularExpr prefix stack in 
    let cycle', _ = recordToRegularExpr cycle (stack@stack') in 
    Concate (prefix', Kleene(cycle'))
  | None -> 
    let nextStates = Procdesc.Node.get_succs currentState in 
    match nextStates with 
    | [] -> 
      let final, _ = recordToRegularExpr (history@[currentState]) stack in 
      final

    | succLi -> 
      let env' = ((history@[currentState], stack)) in 
      let residues = List.map succLi ~f:(fun next -> iterateProc env' next) in 
      let eventTail = disjunctRE residues in 
      eventTail 

let rec findReoccurrenceJoinNodes (history:Procdesc.Node.t list) (currentState:Procdesc.Node.t): int list = 
  let node_key = getNodeID currentState in
  match existRecord history node_key with 
  | Some (_, _) -> [node_key]
  | None -> 
    let nextStates = Procdesc.Node.get_succs currentState in 
    match nextStates with 
    | [] -> []
    | succLi -> 
      let history' = ((history@[currentState])) in 
      let reoccurrences = List.map succLi ~f:(fun next -> findReoccurrenceJoinNodes history' next) in 
      List.fold_left reoccurrences ~init:[] ~f:(fun acc a -> acc @ a)


let findTheNextJoinCycle stack (currentState:Procdesc.Node.t) : stack * regularExpr * Procdesc.Node.t = 
  let rec helper state : (Procdesc.Node.t * Procdesc.Node.t * stack) = 
    match Procdesc.Node.get_succs state with 
    | [succ1;succ2] -> 
      let _, stack' = recordToRegularExpr ([state]) stack in 
      (*
      print_endline ("helper node" ^ string_of_int (getNodeID state) );
      print_endline ((String.concat ~sep:"," (List.map ~f:(fun (x,y) -> Exp.to_string x ^ "->" ^ Ident.to_string y) stack')));
      *)
      (match (Procdesc.Node.get_kind succ1, Procdesc.Node.get_kind succ2) with 
      | (Prune_node(false, _, _), Prune_node(true, _, _)) -> 
        (match (Procdesc.Node.get_succs succ1) with 
        | hd::_ -> hd, succ2, stack'
        | _ -> raise (Failure "findTheNextJoinCycle1")  
        )
      | (Prune_node(true, _, _), Prune_node(false, _, _)) -> 
        (match (Procdesc.Node.get_succs succ2) with 
        | hd::_ -> hd, succ1, stack'
        | _ -> raise (Failure "findTheNextJoinCycle2")  
        )
      | _ -> raise (Failure "findTheNextJoinCycle3") 
      )
    | [hd] -> helper hd
    | _ -> raise (Failure "findTheNextJoinCycle4") 
  in 
  let nextJoin, positiveStarting, stack' = helper currentState in 
  (*print_endline ("negetive node:" ^ string_of_int (getNodeID nextJoin) ^ ", and the postive point:" 
  ^ string_of_int (getNodeID positiveStarting)); 
  print_endline ("current node" ^ string_of_int (getNodeID currentState) );
  print_endline ((String.concat ~sep:"," (List.map ~f:(fun (x,y) -> Exp.to_string x ^ "->" ^ Ident.to_string y) (stack@stack'))));
    *)
  let re = iterateProc ([(currentState)], stack@stack') positiveStarting in 
  stack, re, nextJoin 
  
;;



let rec findTheNextJoin (stack:stack) (loopJoins:int list) (currentState:Procdesc.Node.t) (disjunStack:int list) : stack * regularExpr * Procdesc.Node.t option = 
  let node_kind = Procdesc.Node.get_kind currentState in
  let currentID = getNodeID currentState in
  let helper disjunStackIn : stack * regularExpr * Procdesc.Node.t option = 
    let nextStates = Procdesc.Node.get_succs currentState in 
    let reExtension, stack' = 
      match node_kind with 
      | Join_node | Skip_node _ -> Emp, stack
      | _ ->  recordToRegularExpr ([currentState]) stack in 
    match nextStates with 
    | [] -> 
      stack'@stack, reExtension , None
    | [succ] -> 
      let stack'', re, nextJoin = findTheNextJoin (stack'@stack) loopJoins succ disjunStackIn  in 
      stack'', Concate(reExtension,re), nextJoin
    | [succ1;succ2] ->
      let stack1'', re1, nextJoin1 = findTheNextJoin (stack'@stack) loopJoins succ1 (currentID:: disjunStackIn)  in 
      let stack2'', re2, nextJoin2 = findTheNextJoin (stack'@stack) loopJoins succ2 (currentID:: disjunStackIn)  in 
      
      (match nextJoin1, nextJoin2 with 
      | None, None  -> stack1''@stack2'', Concate(reExtension, Disjunction(re1,re2)), nextJoin1
      | Some join1, Some join2 -> 
        let node_kind_join1 = (Procdesc.Node.get_kind join1) in
        let node_kind_join2 = (Procdesc.Node.get_kind join2) in
        let joinID1 = (getNodeID join1) in
        let joinID2 = (getNodeID join2) in
        (match node_kind_join1, node_kind_join2 with 
        (* here the first two cases are to deal with GOTO statements, although it is not complete still, 
        this implementation is only true if from  the Join_node to the skip there is nothing happending. 
        *)
        | Skip_node _, Join_node -> stack1''@stack2'', Concate(reExtension, Disjunction(re1,re2)), nextJoin1
        | Join_node, Skip_node _ -> stack1''@stack2'', Concate(reExtension, Disjunction(re1,re2)), nextJoin2
        | _, _ -> 
          if joinID1 == joinID2 then ()
          else 
            print_endline (("WARNING!!! findTheNextJoin non consitant join  " ^ string_of_int joinID1 ^ " " ^ string_of_int joinID2));
          stack1''@stack2'', Concate(reExtension, Disjunction(re1,re2)), nextJoin1

        )
        
      | None, Some join | Some join, None  -> 
        stack1''@stack2'', Concate(reExtension, Disjunction(re1,re2)), Some join
      
      )


    | succ:: _  ->
      let stack'', re, nextJoin = findTheNextJoin (stack'@stack) loopJoins succ (currentID:: disjunStackIn) in 
      stack'', Concate(reExtension,re), nextJoin
      

  in 
  
  match node_kind with 
  | Exit_node | Stmt_node ReturnStmt -> (* looping at the last state *)
    let reExtension, stack' = recordToRegularExpr ([currentState]) stack in 
    (stack@stack'), Omega(reExtension), None 

  | Skip_node _ -> stack, Emp, Some currentState

  | Join_node -> 
    if existAux (==) loopJoins currentID then 
      let stack', re, nextJoin = findTheNextJoinCycle stack currentState in 
      stack', re, Some (nextJoin)
    else 
      (match disjunStack with 
      | [] -> raise (Failure "not possible, there is a join node without any disjunction in front")
      | [_] -> 
        stack, Emp, Some currentState
      | _::tail -> helper tail

      )
  | _ -> helper disjunStack 
  
;;

let rec getRegularExprFromCFG_helper (loopJoins:int list) (history:regularExpr) stack (currentState:Procdesc.Node.t): (regularExpr * stack) = 
  let node_kind = Procdesc.Node.get_kind currentState in
  let currentID = getNodeID currentState in
  (match node_kind with 

  | Exit_node | Stmt_node ReturnStmt -> (* looping at the last state *)
    let reExtension, stack' = recordToRegularExpr ([currentState]) stack in 
    (Concate (history, Omega(reExtension)), (stack@stack'))

  | _ -> 
    if existAux (==) loopJoins currentID then 
      (let stack', re, nextJoin = findTheNextJoinCycle stack currentState in 
      let history' = Concate (history, (re)) in 
      getRegularExprFromCFG_helper loopJoins history' (stack@stack') nextJoin )
    else 
    let reExtension, stack' = recordToRegularExpr ([currentState]) stack in 
    let history' = Concate (history, reExtension) in
    let stack'' = (stack@stack') in 
    let nextStates = Procdesc.Node.get_succs currentState in 
    match nextStates with 
    | [] -> (history' , stack'')
    | [succ] -> getRegularExprFromCFG_helper loopJoins history' stack'' succ 
    | [succ1;succ2] -> (* if else branch *)

      let s1, re1,(join1:Procdesc.Node.t option) = findTheNextJoin stack'' loopJoins succ1 [currentID] in 
      let s2, re2, (join2:Procdesc.Node.t option) = findTheNextJoin stack'' loopJoins succ2 [currentID] in 
      let stack3 = stack''@s1@s2 in 
      (match join1, join2 with 
      | Some join1, Some join2 -> 
        let reDisjunction = Disjunction(re1, re2) in 

        let node_kind_join1 = (Procdesc.Node.get_kind join1) in
        let node_kind_join2 = (Procdesc.Node.get_kind join2) in

        let joinID1 = (getNodeID join1) in
        let joinID2 = (getNodeID join2) in
        (match node_kind_join1, node_kind_join2 with 
        (* here the first two cases are to deal with GOTO statements, although it is not complete still, 
        this implementation is only true if from  the Join_node to the skip there is nothing happending. 
        *)
        | Skip_node _, Join_node -> getRegularExprFromCFG_helper loopJoins (Concate(history', reDisjunction)) stack'' join1
        | Join_node, Skip_node _ -> getRegularExprFromCFG_helper loopJoins (Concate(history', reDisjunction)) stack'' join2
        | _, _ -> 
          if joinID1 == joinID2 then 
            getRegularExprFromCFG_helper loopJoins (Concate(history', reDisjunction)) stack'' join1
          else 
        let info = string_of_int currentID ^ " join at " ^ string_of_int joinID1 ^ " and " ^ string_of_int joinID2 in 
        print_endline (info);
        
            let re1', stack1'''= getRegularExprFromCFG_helper loopJoins re1 stack'' join1 in 
            let re2', stack2''' = getRegularExprFromCFG_helper loopJoins re2 stack'' join2 in 
            Concate(history', Disjunction (re1', re2')) , stack1''' @ stack2'''


        )
        


      | None, None -> 
        let reDisjunction = Disjunction(re1, re2) in 
        Concate(history', reDisjunction), stack3
      | None, Some joinNext -> 
        let secondContinue, stackSND = getRegularExprFromCFG_helper loopJoins re2 stack3 joinNext in 
        Concate(history', Disjunction(re1, secondContinue)), stack3@ stackSND

      | Some joinNext, None -> 
        let secondContinue, stackFST = getRegularExprFromCFG_helper loopJoins re1 stack3 joinNext in 
        Concate(history', Disjunction(re2, secondContinue)), stack3@ stackFST

        
        

      )

    | _ -> raise (Failure "more successors")
     
  )

let getRegularExprFromCFG (procedure:Procdesc.t) : regularExpr = 
  let startState = Procdesc.get_start_node procedure in 
  let reoccurs = sort_uniq (-) (findReoccurrenceJoinNodes [] startState) in 
  (*let _ = List.map reoccurs ~f:(fun a -> print_endline ("reoccurrance" ^ string_of_int a)) in  *)
  let r, _ = getRegularExprFromCFG_helper reoccurs Emp [] startState in 
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

let rec makeAGuess (pi:pure) : terms option = 
  match pi with 
  | LtEq (t, Basic (BINT 0)) 
  | Lt (t, Basic (BINT 0)) -> Some (Minus(Basic (BINT 0), t))
  | GtEq (t, Basic (BINT 0)) 
  | Gt (t, Basic (BINT 0)) -> Some t 
  | PureAnd (p1, p2) 
  | PureOr (p1, p2) -> 
    (match makeAGuess p1, makeAGuess p2 with 
    | Some t1, _ 
    | _, Some t1 -> Some t1
    | _, _-> None 
    )
  | _ -> None 
  
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
  

let updateStateBasedOnCurrentValues (state:((terms * terms)list)) (target:terms) (newValue:terms) : ((terms * terms)list) = 
  let rec subsititude (t:terms) : terms = 
    match findStateRecord t state with 
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
  let updateTransitionPath acc pi = List.map acc ~f:(fun (pAcc, state) -> (PureAnd(pAcc, pi), state)) in 
  let updateTransitionStates acc pi = 
    match pi with 
    | Eq (t1, t2) -> 
      List.map acc ~f:(
      fun (pAcc, state) -> 
        let state' = updateStateBasedOnCurrentValues state t1 t2 in 
        (pAcc, state')) 
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

let wp4Termination (re:regularExpr) (guard:pure) (rankingFun:terms option) : pure = 
  match rankingFun with 
  | None -> FALSE
  | Some rankingTerm -> 
    let (transitionSummary:transitionSummary) = transitionSummary re in 
    print_endline ("current ranking function is " ^ string_of_terms rankingTerm); 
    let (precondition: pure option) = List.fold_left transitionSummary ~init:None 
      ~f:(fun acc (path, stateLi) -> 
      print_endline (string_of_transitionSummary [(path, stateLi)]);
      let (pureIter:pure option) = 
        match findStateRecord rankingTerm stateLi with 
        | None -> Some (Ast_utility.FALSE) (*print_endline("the rancking function did not decreace at all")*)
        | Some (rankingTerm', _) -> 
          let left_hand_side = PureAnd (guard, path) in 
          let right_hand_side = Gt(normalise_terms (Minus(rankingTerm, rankingTerm')), Basic(BINT 0))in 
          let res = entailConstrains left_hand_side right_hand_side in 
          if res then None 
          else Some right_hand_side
      in 
      match acc, pureIter with 
      | Some a, None 
      | None, Some a -> Some a 
      | None , None -> None 
      | Some a, Some b -> Some (PureAnd(a, b))
    ) 
    in 
    match precondition with 
    | None -> TRUE 
    | Some pre -> pre 

let getLoopSummary (re:regularExpr) (path:pure): regularExpr =  
  let re = normalise_es re in
  print_endline ("getLoopSummary " ^ string_of_regularExpr (re));
  let (fstSet:(fstElem list)) = fst re in 
  let fstSet' = removeRedundant fstSet compareEvent in 
  let pi, deriv, rankingFun, loc =  (match fstSet' with 
  | [GuardEv (pi, loc)] ->  
    let f = GuardEv (pi, loc) in 
    let (rankingFun:terms option) = makeAGuess pi in 
    let deriv = normalise_es (derivitives f re) in 
    pi, deriv, rankingFun, loc

  | [PureEv (_, loc)] -> raise (Failure "loop starting with PureEv") (*Ast_utility.TRUE, re, None, loc *)
  
  | _-> raise (Failure "loop starting with more than one fst")
  )
  in 



  print_endline ("loop guard " ^ string_of_pure pi );
  let defaultTerminating = eventToRe (GuardEv (Neg (pi), loc)) in 
  let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
  let stateAfterTerminate = Singleton(Neg (pi), !allTheUniqueIDs) in 
  let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
  let stateWhenNonTerminate = match pi with | TRUE -> deriv | _ -> re in 
  (match wp4Termination deriv (PureAnd(pi, path)) rankingFun with 
  | FALSE -> 
    (match pi with 
    | TRUE  -> Omega (stateWhenNonTerminate)
    | _ -> Disjunction (Omega (stateWhenNonTerminate), defaultTerminating)
    )
  | TRUE -> Concate (defaultTerminating, stateAfterTerminate)
  | weakestPre -> 
    let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
    let terminating = eventToRe (GuardEv (PureAnd(pi, conjunctPure path weakestPre), !allTheUniqueIDs))  in 
    let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
    let non_termination_guard = eventToRe (GuardEv (PureAnd(pi, conjunctPure path (normalise_pure (Neg weakestPre))), !allTheUniqueIDs)) in 
    let non_terminating = Omega (Concate(non_termination_guard, stateWhenNonTerminate )) in 
    disjunctRE [
      Concate (Disjunction(defaultTerminating, terminating), stateAfterTerminate); non_terminating]
  )



  
let rec convertAllTheKleeneToOmega (re:regularExpr) (path:pure): regularExpr * pure = 
  match re with 
  | Kleene (reIn) -> 
    let normalForm = normaliseTheDisjunctions (deleteAllTheJoinNodes reIn) in 
    let loopsummary = getLoopSummary normalForm (normalise_pure path) in 
    print_endline ("before loopsummary: " ^ string_of_pure  path);
    print_endline ("loopsummary: " ^ string_of_regularExpr loopsummary);
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
  | Omega reIn | Kleene reIn -> recordTheMaxValue4RE reIn 
  | Bot | Emp -> ()


let computeSummaryFromCGF (procedure:Procdesc.t) : regularExpr = 
  (*
  let localVariables = Procdesc.get_locals procedure in 
  let _ = List.map ~f:(fun var -> print_endline (Mangled.to_string var.name ^"\n") ) localVariables in  
  *)
  let pass1 =  normalise_es (getRegularExprFromCFG procedure) in 
  let pass3 =  ( ( pass1)) in 
  recordTheMaxValue4RE pass3; 
  let pass3', _ = convertAllTheKleeneToOmega pass3 (Ast_utility.TRUE) in 
  let pass4 = normalise_es (pass3') in  (*this is the step for sumarrizing the loop*)
  print_endline ("\n"^string_of_regularExpr (pass4)^ "\n------------"); 

  pass4
  ;;

let rec findRelaventValueSetFromTerms (t:terms) (var:string) : int list = 
  match t with 
  | Basic (BINT n) -> [n](*[n+1 ; n; n-1]*)
  | Plus (t1, t2) 
  | Minus (t1, t2) -> findRelaventValueSetFromTerms t1 var @ findRelaventValueSetFromTerms t2 var 
  | _ -> []

let rec findRelaventValueSetFromPure (p:pure) (var:string) : int list = 
  match p with 
  | Eq (Basic (BVAR s), t2) 
  | Gt (Basic (BVAR s), t2)  
  | LtEq (Basic (BVAR s), t2) ->  
    if String.compare s var == 0 then 
      let seeds = findRelaventValueSetFromTerms t2 var in 
      List.fold_left seeds ~init:[] ~f:(fun acc n -> acc @ [n; n+1])
      else [] 
  | GtEq (Basic (BVAR s), t2) 
  | Lt (Basic (BVAR s), t2) ->
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

let rec getAllPathConditionsCTL (ctls:ctl list): pure list = 
  List.fold_left ~init:[] ~f:(fun acc ctl -> acc @ getAllPureFromCTL ctl) ctls 

let rec getUnknownVars (re:regularExpr): string list = 
  match re with 
  | Singleton (Eq (Basic(BVAR var), Basic ANY), _)  -> [var]
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

let rec pureOfCurrentState (currentValuation: (string * basic_type) list) : pure = 
  match currentValuation with 
  | [] -> TRUE 
  | (var, n):: xs-> PureAnd(Eq(Basic (BVAR var), Basic n), pureOfCurrentState xs) 

let rec pureOfPathConstrints (currentValuation: (pure) list) : pure = 
  match currentValuation with 
  | [] -> TRUE 
  | p:: xs-> PureAnd(p, pureOfPathConstrints xs) 

  

(* predicates are the precicates derived from the program, whereas the 
   predicatesSpec are the precicates derived from the specifiction, 
   the difference is that precicates needs to be sampled at the start location, 
   where as predicatesSpec only matters to generate facts for PureEv
*)
let rec getFactFromPureEv (p:pure) (state:int) (predicates:pure list) (predicatesSpec:pure list) (pathConstrint: (pure list)) (currentValuation: (string * basic_type) list): (((string * basic_type) list) * relation list)= 
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
  | Eq (Basic(BVAR _), Basic (ANY)) ->  currentValuation, []

  (* assign concret value *)
  | Eq (Basic(BVAR var), Basic t1) -> 

    let currentValuation' = updateCurrentValuation currentValuation var t1 in 
    print_endline (List.fold_left ~init:"currentValuation' " ~f:(fun acc (var, value) -> acc ^ (", " ^ var ^"=" ^ string_of_basic_t value)) currentValuation'); 

    let pureOfCurrentState = pureOfCurrentState currentValuation' in 
    let pathConstrint' = removeConstrint pathConstrint var in 
    let currentConstraint = PureAnd(pureOfCurrentState, pathConstrint') in 
    print_endline ("currentConstraint: " ^ string_of_pure currentConstraint);
    
    let predicates' = 
        if entailConstrains currentConstraint FALSE 
        (* this is because sometimes the actual valuation of the state and the path constaint conjuncs to false, in that case, we only keep the structure *)
        then List.filter ~f:(fun ele -> relevent ele var && entailConstrains pureOfCurrentState ele) (predicates@predicatesSpec) 
        else List.filter ~f:(fun ele -> relevent ele var && entailConstrains currentConstraint ele) (predicates@predicatesSpec) in 
    let facts = flattenList (List.map ~f:(fun ele -> getFactFromPure ele state) predicates') in 
    currentValuation', facts

  | Predicate (s, terms) -> 
    if twoStringSetOverlap [s] [entryKeyWord] 
    then currentValuation, ([(s, terms@[loc])] @ flattenList (List.map ~f:(fun ele -> getFactFromPure ele state) predicates))
    else currentValuation, [(s, terms@[loc])] 
      

  | _ -> currentValuation, []
  ;;

let rec pureToBodies (p:pure) (s:int option): body list = 
  match s with 
  | None  -> [] 
  | Some state -> 
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

let rec lookforExistingMapping li (n:int) : int option  = None 
    (*match li with 
    | [] -> None 
    | (n1, n2):: xs  -> if n1 == n then Some n2 else lookforExistingMapping xs n 
*)

let rec instantiateREStatesWithFreshNum reIn (record:((int * int )list)): regularExpr * ((int * int )list )= 
  match reIn with 
  | Bot           
  | Emp   -> reIn, record
  | Guard (p, state) -> 
    (match lookforExistingMapping record state with
    | None -> 
      let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
      let stateNew = !allTheUniqueIDs in 
      let record' = (state, stateNew) :: record in 
      Guard (p, stateNew) , record' 

    | Some stateNew -> Guard (p, stateNew) , record 
    ) 
    

  | Singleton (p, state)  -> 
    (match lookforExistingMapping record state with
    | None -> 
      let () = allTheUniqueIDs := !allTheUniqueIDs + 1 in 
      let stateNew = !allTheUniqueIDs in 
      let record' = (state, stateNew) :: record in 
      Singleton (p, stateNew) , record' 

    | Some stateNew -> Singleton (p, stateNew) , record 
    ) 
  | Concate (eff1, eff2) -> 
    let re1, record1 = instantiateREStatesWithFreshNum eff1 record in 
    let re2, record2 = instantiateREStatesWithFreshNum eff2 record1 in 
    Concate (re1, re2), record2
    
  | Disjunction (eff1, eff2) ->
    let re1, record1 = instantiateREStatesWithFreshNum eff1 record in 
    let re2, record2 = instantiateREStatesWithFreshNum eff2 record1 in 
    Disjunction (re1, re2), record2
  | Kleene effIn          ->
     let re1, record1 = instantiateREStatesWithFreshNum effIn record in 
     Kleene re1, record1
     
  | Omega effIn          ->
    let re1, record1 = instantiateREStatesWithFreshNum effIn record in 
    Omega re1, record1





let convertRE2Datalog (re:regularExpr) (specs:ctl list): (relation list * rule list) = 

  let (doneDelimiters:int list ref) = ref[] in 
  let pathConditions = getAllPathConditions re in 
  let (pathConditionsSpec:pure list) = getAllPathConditionsCTL specs in 
  (* decomposedPathConditions: this is to sample the constraints from the path *)
  let (decomposedPathConditions:pure list) = removeRedundant (flattenList (List.map ~f:(fun p -> decomposePure p ) (pathConditions) )) comparePure in 
  
  let (decomposedpathConditionsSpec:pure list) = removeRedundant (flattenList (List.map ~f:(fun p -> decomposePure p ) (pathConditionsSpec) )) comparePure in 
(* decomposedPathConditions are the precicates derived from the program, whereas the 
   decomposedpathConditionsSpec are the precicates derived from the specifiction, 
*)
  
  print_endline ("decomposedPathConditions\n" ^ (String.concat ~sep:",\n" (List.map ~f:(fun p -> string_of_pure p) (decomposedPathConditions@decomposedpathConditionsSpec))));   


  let rec mergeResults li (acca, accb) = 
    match li with 
    | [] -> (acca, accb) 
    | (a, b) :: xs -> mergeResults xs (acca@a, accb@b )
  in     
  let rec ietrater reIn (previousState:int option) (pathConstrint: (pure list)) (currentValuation: (string * basic_type) list) : (relation list * rule list) = 
    let reIn = normalise_es reIn in 
    (*print_endline ( string_of_regularExpr reIn );    *)

    
    let fstSet = removeRedundant (fst reIn) compareEvent in 
    match fstSet with 
    | [] -> 
      (match previousState with 
      | Some previousState -> 
        let stateFact = (stateKeyWord, [Basic (BINT previousState)]) in 
        ([stateFact], [])
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
              | bodies -> [stateFact], [(fact', flattenList(List.map ~f:(fun a -> (pureToBodies a (Some previousState))) bodies))]
              )
              

            | None  -> [], []
            )
          in 
          let (reAcc'', ruAcc'') = 
            if existAux (==) !doneDelimiters state then [], []
            else 
              (doneDelimiters := state:: !doneDelimiters;
              ietrater (derivitives f reIn) (Some state) []) currentValuation in 
          
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
              | bodies -> [stateFact], [(fact', flattenList(List.map ~f:(fun a -> (pureToBodies a (Some previousState))) bodies))]
              )
            | None -> [], []) in 
          let currentValuation', valueFacts = getFactFromPureEv p state decomposedPathConditions decomposedpathConditionsSpec pathConstrint currentValuation in 
          print_endline (List.fold_left ~init:"valueFacts " ~f:(fun acc value -> acc ^ (", " ^ string_of_relation value)) valueFacts); 

          let (derivitives:regularExpr) = 
            let original = (derivitives f reIn) in original
          in 

          let pathConstrint' = 
            match p with 
            | Predicate (s, _) -> if String.compare s joinKeyword == 0 then [] else pathConstrint
            | _ -> pathConstrint
          in 


          let (reAcc'', ruAcc'') = ietrater derivitives (Some state) pathConstrint' currentValuation' in 
          mergeResults [(reAcc, ruAcc); (reAcc', ruAcc'); (valueFacts, []); (reAcc'', ruAcc'')] ([], [])

          
        | GuardEv (guard, state) ->  
          (*print_endline ("GuardEv " ^ string_of_pure guard ); *)
          let currentGuardBody = (pureToBodies guard (previousState)) in 
          let (reAcc', ruAcc')  = 
            (match previousState with 
            | Some previousState -> 
              (*let fact = (flowKeyword, [Basic (BINT previousState); Basic (BINT state)]) in *)
              let fact' = (controlFlowKeyword, [Basic (BINT previousState); Basic (BINT state)]) in 

              let stateFact = (stateKeyWord, [Basic (BINT previousState)]) in 
              (match pathConstrint with 
              | [] -> [stateFact], [(fact', currentGuardBody)]
              | bodies -> [stateFact], [(fact', flattenList(List.map ~f:(fun a -> (pureToBodies a (Some previousState))) bodies) @ currentGuardBody)]
              )
            | None -> [], []) 
          in 
          let (pathConstrint': (pure list)) = 
            match pathConstrint with 
            | [] -> ([guard])
            | bodies -> (bodies @ [guard])
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
  print_endline ("allVarSpec:\n" ^ (String.concat ~sep:",\n" (List.map ~f:(fun p -> string_of_pure p) allVarSpec)));   

  let rec partitionRE reIn :  regularExpr list = 
    match reIn with 
    | Concate (re1, re2) -> partitionRE re1  @ partitionRE re2
    | _ -> [reIn]
  in 
  let segemants = partitionRE re in 

  print_endline ("\nsegemants:\n" ^ (String.concat ~sep:",\n" (List.map ~f:(fun p -> string_of_regularExpr p) segemants)) ^ "\n");
  
  let rec iteraterSegemnst reInLi : regularExpr = 
    match reInLi with 
    | Disjunction(es1, es2) :: xs -> 
      let x = Disjunction(es1, es2) in 
      let containRelevantPure = containRelevantPureRE x allVarSpec in 
      if containRelevantPure then 
        let derivitives = iteraterSegemnst xs in  
        print_endline ("derivitives " ^ string_of_regularExpr derivitives);  
        let derivitives1, _ = instantiateREStatesWithFreshNum (Concate (x, derivitives)) [] in 
        print_endline ("after  " ^ string_of_regularExpr derivitives1);  

        derivitives1

      else Concate (x, iteraterSegemnst xs)
    | [x] ->  x
    | x :: xs  -> Concate (x, iteraterSegemnst xs)
    | [] -> Emp
  in 

  iteraterSegemnst segemants

  


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

  let summaries = (Cfg.fold_sorted cfg ~init:[] 
    ~f:(fun accs procedure -> 
      print_endline ("\n//-------------\nFor procedure: " ^ Procname.to_string (Procdesc.get_proc_name procedure) ^":" );
      let summary = computeSummaryFromCGF procedure in 
      List.append accs [summary] )) 
  in


  let (factPrinting: string list) = flattenList (List.map summaries ~f: (fun summary -> 
      let summary' = createNecessaryDisjunction summary specifications in
      let (facts, rules) = convertRE2Datalog (summary') specifications in 
      ("/*" ^ string_of_regularExpr summary ^ "*/") :: 
      ("/*" ^ string_of_regularExpr summary' ^ "*/") :: 
      string_of_facts (sortFacts facts) :: 
      string_of_rules (sortRules rules) :: []
  )) in 

  
  let (specPrinting:string list) = List.map specifications ~f:(fun ctl -> "//" ^ string_of_ctl ctl) in 

  let predicateDeclearation = (sort_uniq (fun (a, _) (c, _) -> String.compare a c) !predicateDeclearation) in 

  let (datalogProgPrinting:string list) = 
    flattenList (List.map specifications 
    ~f:(fun item -> 
      let fname, program = (translation item) in 
      (*print_endline (string_of_datalog program);
      print_endline (".output "^ fname ^"Final(IO=stdout)\n") *)
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
     
  let () = totol_Lines_of_Spec := !totol_Lines_of_Spec + lines_of_spec in 


  let facts = (Cfg.fold_sorted cfg ~init:[] 
    ~f:(fun facts procedure -> List.append facts (get_facts procedure) )) in
  Out_channel.write_lines (source_Address ^ ".dl") 
  (factPrinting@specPrinting@datalogProgPrinting @ ["/* Other information \n"]@facts@["*/\n"] );


  print_endline ("\nTotol_execution_time: " ^ string_of_float ((Unix.gettimeofday () -. start) (* *.1000. *) ) ^ " s"); 

  print_endline ("\n========================================================================="); 
  print_endline ("<== Run$ souffle -F. -D. " ^ source_Address ^ ".dl" ^ " ==>");

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
