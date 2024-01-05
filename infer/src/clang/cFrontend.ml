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



let string_of_source_range ((s1, s2):Clang_ast_t.source_range) :string = 
  match (s1.sl_file, s2.sl_file) with 
  | (Some name, _) 
  | (_, Some name) -> name
  | (_, _) -> "none"



let stmt2Term_helper (op: string) (t1: terms option) (t2: terms option) : terms option = 
  match (t1, t2) with 
  | (None, _) 
  | (_, None ) -> None 
  | (Some t1, Some t2) -> 
    let p = 
      if String.compare op "+" == 0 then Plus (t1, t2)
    else Minus (t1, t2)
    in Some p 

let rec stmt2Term (instr: Clang_ast_t.stmt) : terms option = 
  (*print_endline ("term kind:" ^ Clang_ast_proj.get_stmt_kind_string instr);
*)
  match instr with 
  | ImplicitCastExpr (_, x::_, _, _, _) 
    -> 
    stmt2Term x
  | CStyleCastExpr (_, x::rest, _, _, _) 
  | ParenExpr (_, x::rest, _) -> 
  (*print_string ("ParenExpr/CStyleCastExpr: " ^ (
    List.fold_left (x::rest) ~init:"" ~f:(fun acc a -> acc ^ "," ^ Clang_ast_proj.get_stmt_kind_string a)
  )^ "\n");
  *)

    stmt2Term x
  
  | BinaryOperator (stmt_info, x::y::_, expr_info, binop_info)->
  (match binop_info.boi_kind with
  | `Add -> stmt2Term_helper "+" (stmt2Term x) (stmt2Term y) 
  | `Sub -> stmt2Term_helper "" (stmt2Term x) (stmt2Term y) 
  | _ -> None 
  )
  | IntegerLiteral (_, stmt_list, expr_info, integer_literal_info) ->
    Some (Basic(BINT (int_of_string(integer_literal_info.ili_value))))

  | DeclRefExpr (stmt_info, _, _, decl_ref_expr_info) -> 
  let (sl1, sl2) = stmt_info.si_source_range in 

  (match decl_ref_expr_info.drti_decl_ref with 
  | None -> None 
  | Some decl_ref ->
    (
    match decl_ref.dr_name with 
    | None -> None
    | Some named_decl_info -> Some (Basic(BVAR (named_decl_info.ni_name)))
      
    )
  )
  | NullStmt _ -> Some (Basic(BVAR ("NULL")))
  | MemberExpr (_, arlist, _, member_expr_info)  -> 
    let memArg = member_expr_info.mei_name.ni_name in 
    let temp = List.map arlist ~f:(fun a -> stmt2Term a) in 
    let name  = List.fold_left temp ~init:"" ~f:(fun acc a -> 
    acc ^ (
      match a with
      | None -> "_"
      | Some t -> string_of_terms t ^ "_"
    )) in 
    Some (Basic(BVAR(name^memArg)))

  | ArraySubscriptExpr (_, arlist, _)  -> 
    let temp = List.map arlist ~f:(fun a -> stmt2Term a) in 
    (*print_endline (string_of_int (List.length temp)); *)
    let name  = List.fold_left temp ~init:"" ~f:(fun acc a -> 
    acc ^ (
      match a with
      | None -> "_"
      | Some t -> string_of_terms t ^ "_"
    )) in 
    Some (Basic(BVAR(name)))

  | UnaryOperator (stmt_info, x::_, expr_info, op_info) ->
    stmt2Term x 
      

  | _ -> Some (Basic(BVAR(Clang_ast_proj.get_stmt_kind_string instr))) 



let rec string_of_decl (dec :Clang_ast_t.decl) : string = 
  match dec with 
  | VarDecl (_, ndi, qt, vdi) -> 
    ndi.ni_name ^ "::" ^ Clang_ast_extend.type_ptr_to_string qt.qt_type_ptr
    ^" "^ (match vdi.vdi_init_expr with 
    | None -> ""
    | Some stmt -> string_of_stmt stmt)

    (* clang_prt_raw 1305- int, 901 - char *)
  | _ ->  Clang_ast_proj.get_decl_kind_string dec

and string_of_stmt_list (li: Clang_ast_t.stmt list) sep : string = 
    match li with 
  | [] -> ""
  | [x] -> string_of_stmt x 
  | x::xs -> string_of_stmt x ^ sep ^ string_of_stmt_list xs sep

and string_of_stmt (instr: Clang_ast_t.stmt) : string = 
  let rec helper_decl li sep = 
    match li with 
  | [] -> ""
  | [x] -> string_of_decl  x 
  | x::xs -> string_of_decl  x ^ sep ^ helper_decl xs sep
  in 
(*
  let rec helper li sep = 
    match li with 
  | [] -> ""
  | [x] -> string_of_stmt x 
  | x::xs -> string_of_stmt x ^ sep ^ helper xs sep
  in 
*)
  match instr with 
  | ReturnStmt (stmt_info, stmt_list) ->
    "ReturnStmt " ^ string_of_stmt_list stmt_list " " 

  (*
  | MemberExpr (stmt_info, stmt_list, _, member_expr_info) ->
    "MemberExpr " ^ string_of_stmt_list stmt_list " " 
    *)

  | MemberExpr (_, arlist, _, member_expr_info)  -> 
    let memArg = member_expr_info.mei_name.ni_name in 
    let temp = List.map arlist ~f:(fun a -> stmt2Term a) in 
    let name  = List.fold_left temp ~init:"" ~f:(fun acc a -> 
    acc ^ (
      match a with
      | None -> "_"
      | Some t -> string_of_terms t ^ "_"
    )) in name^memArg

  | IntegerLiteral (_, stmt_list, expr_info, integer_literal_info) ->
    "IntegerLiteral " ^ integer_literal_info.ili_value

  | StringLiteral (_, stmt_list, expr_info, str_list) -> 
    let rec straux li = 
      match li with 
      | [] -> ""
      | x :: xs  -> x  ^ " " ^ straux xs 
    in (* "StringLiteral " ^ string_of_int (List.length stmt_list)  ^ ": " ^ *) straux str_list


  | UnaryOperator (stmt_info, stmt_list, expr_info, unary_operator_info) ->
    "UnaryOperator " ^ string_of_stmt_list stmt_list " " ^ ""
  
  | ImplicitCastExpr (stmt_info, stmt_list, expr_info, cast_kind, _) -> 
    (*"ImplicitCastExpr " ^*) string_of_stmt_list stmt_list " " 
  | DeclRefExpr (stmt_info, _, _, decl_ref_expr_info) ->
    (*"DeclRefExpr "^*)
    (match decl_ref_expr_info.drti_decl_ref with 
    | None -> "none"
    | Some decl_ref ->
      (
        match decl_ref.dr_name with 
        | None -> "none1"
        | Some named_decl_info -> named_decl_info.ni_name
      )
    )

  | ParenExpr (stmt_info (*{Clang_ast_t.si_source_range} *), stmt_list, _) ->

    "ParenExpr " ^ string_of_source_range  stmt_info.si_source_range
    ^ string_of_stmt_list stmt_list " " 

    
  | CStyleCastExpr (stmt_info, stmt_list, expr_info, cast_kind, _) -> 
  "CStyleCastExpr " ^ string_of_stmt_list stmt_list " " ^ ""


  | IfStmt (stmt_info, stmt_list, if_stmt_info) ->

  "IfStmt " ^ string_of_stmt_list stmt_list "," ^ ""
 
  | CompoundStmt (_, stmt_list) -> string_of_stmt_list stmt_list "; " 

  | BinaryOperator (stmt_info, stmt_list, expr_info, binop_info) -> 
   "BinaryOperator " ^ string_of_stmt_list stmt_list (" "^ Clang_ast_proj.string_of_binop_kind binop_info.boi_kind ^" ")  ^""

  | DeclStmt (stmt_info, stmt_list, decl_list) -> 
  "DeclStmt " (*  ^ string_of_stmt_list stmt_list " " ^ "\n"^
    "/\\ "^ string_of_int stmt_info.si_pointer^ " " *)  ^ helper_decl decl_list " " ^ "" 
  
  | CallExpr (stmt_info, stmt_list, ei) -> 
      (match stmt_list with
      | [] -> assert false 
      | x :: rest -> 
    "CallExpr " ^ string_of_stmt x ^" (" ^  string_of_stmt_list rest ", " ^ ") "
)

  | ForStmt (stmt_info, [init; decl_stmt; condition; increment; body]) ->
    "ForStmt " ^  string_of_stmt_list ([body]) " " 

  | WhileStmt (stmt_info, [condition; body]) ->
    "WhileStmt " ^  string_of_stmt_list ([body]) " " 
  | WhileStmt (stmt_info, [decl_stmt; condition; body]) ->
    "WhileStmt " ^  string_of_stmt_list ([body]) " " 

  | RecoveryExpr _ -> "RecoveryExpr"
  | BreakStmt _ -> "BreakStmt"


  | _ -> "not yet " ^ Clang_ast_proj.get_stmt_kind_string instr;;





let rec extractEventFromFUnctionCall (x:Clang_ast_t.stmt) (rest:Clang_ast_t.stmt list) : event option = 
(match x with
| DeclRefExpr (stmt_info, _, _, decl_ref_expr_info) -> 
  let (sl1, sl2) = stmt_info.si_source_range in 
  let (lineLoc:int option) = sl1.sl_line in 

  (match decl_ref_expr_info.drti_decl_ref with 
  | None -> None  
  | Some decl_ref ->
    (
    match decl_ref.dr_name with 
    | None -> None 
    | Some named_decl_info -> 
      Some (named_decl_info.ni_name, argumentsTerms2basic_types((
        List.map rest ~f:(fun r -> stmt2Term r))))
    )
  )

| ImplicitCastExpr (_, stmt_list, _, _, _) ->
  (match stmt_list with 
  | [] -> None 
  | y :: restY -> extractEventFromFUnctionCall y rest)
| _ -> None 
)

let getFirst (a, _) = a

let conjunctPure (pi1:pure) (pi2:pure): pure = 
  if entailConstrains pi1 pi2 then pi1 
        else if entailConstrains pi2 pi1 then pi2
        else  PureAnd (pi1, pi2)



let rec findReturnValue (pi:pure) : terms option = 
  match pi with
  | Eq (Basic (BRET), t2) 
  | Eq (t2, Basic (BRET)) -> Some t2 
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


let rec stmt2Pure (instr: Clang_ast_t.stmt) : pure option = 
  (* print_endline (Clang_ast_proj.get_stmt_kind_string instr); *)

  match instr with 
  | BinaryOperator (stmt_info, x::y::_, expr_info, binop_info)->
    (match binop_info.boi_kind with
    | `LT -> stmt2Pure_helper "<" (stmt2Term x) (stmt2Term y) 
    | `GT -> stmt2Pure_helper ">" (stmt2Term x) (stmt2Term y) 
    | `GE -> stmt2Pure_helper ">=" (stmt2Term x) (stmt2Term y) 
    | `LE -> stmt2Pure_helper "<=" (stmt2Term x) (stmt2Term y) 
    | `EQ -> stmt2Pure_helper "=" (stmt2Term x) (stmt2Term y) 
    | `NE -> stmt2Pure_helper "!=" (stmt2Term x) (stmt2Term y) 
    | _ -> None 
    )

  | ImplicitCastExpr (_, x::_, _, _, _) -> stmt2Pure x
  | UnaryOperator (stmt_info, x::_, expr_info, op_info)->
    (match op_info.uoi_kind with
    | `Not -> 
      (match stmt2Pure x with 
      | None -> None 
      | Some p -> Some (Neg p))
    | `LNot -> 
      (match stmt2Term x with 
      | None -> None 
      | Some t -> Some (Eq(t, Basic(BINT 0)))
      )
      
    | _ -> 
      print_endline ("`LNot DeclRefExpr none4"); 
      None
    )
  | ParenExpr (_, x::rest, _) -> stmt2Pure x
  
  | _ -> Some (Gt ((Basic( BVAR (Clang_ast_proj.get_stmt_kind_string instr))), Basic( BVAR ("null"))))




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

 

let int_of_intList intop = 
  match intop with 
  | []  -> (-1)
  |i ::_ -> i ;;

let rec getLastEle (li:basic_type list) :  basic_type option  = 
  match li with 
  | [] -> None 
  | [l] -> Some l 
  | _ :: xs -> getLastEle xs 

let rec lastLocOfFact (facts: fact list) = 
  match facts with 
  | [] -> [] 
  | (str, argLi) :: xs  -> 
    if String.compare str "flow" == 0 then lastLocOfFact xs  
    else 
    (match getLastEle argLi with 
    | Some (BINT i) -> i :: (lastLocOfFact xs)
    | _ -> lastLocOfFact xs 
    )


let rec syh_compute_stmt_facts (current:programState) (env:(specification list)) (instr: Clang_ast_t.stmt) : programStates = 
  let (currentfacts, currentExitCode, currentreachableState) = current in 
  (* print_endline ("Facts. " ^ ": "^ (Clang_ast_proj.get_stmt_kind_string instr)); *)
  if currentExitCode == 1 then [current] 
  else 
  match instr with 
  | CompoundStmt (stmt_info, stmt_list) -> 

    let rec helper acc stmtList = 
      match stmtList with 
      | [] -> [acc] 
      | x :: xs  -> 
        let programStatesX = syh_compute_stmt_facts acc env x in 
        let programStatesXS = List.map programStatesX ~f:(fun state -> helper state xs) in 
        flattenList programStatesXS 
    in 
    helper current stmt_list 

  | DeclStmt (_, [CStyleCastExpr(_, [(CallExpr (stmt_info, stmt_list, ei))], _, _, _)], [del])  
  | DeclStmt (_, [(CallExpr (stmt_info, stmt_list, ei))], [del]) 
  | DeclStmt (_, [(ImplicitCastExpr (_, [(CallExpr (stmt_info, stmt_list, ei))], _, _, _))], [del]) ->

      let () = handlerVar := Some (string_of_decl del) in 
      let stmt = (Clang_ast_t.CallExpr (stmt_info, stmt_list, ei)) in 
      syh_compute_stmt_facts current env stmt

(*| CallExpr (stmt_info, stmt_list, ei) -> 
    let (fp, _) = stmt_intfor2FootPrint stmt_info in 
    let fp = (int_of_intList fp) in 
    
    (* STEP 0: retrive the spec of the callee *)
    let (facts, nextRechable) = 
      match stmt_list with 
      | [] -> assert false  
      | x::rest -> 
        (match extractEventFromFUnctionCall x rest with 
        | None -> ([], currentreachableState)
        | Some (calleeName, acturelli) -> (* arli is the actual argument *)
          
          (*let () = print_string ("=========================\n") in 
          print_string (string_of_event (calleeName, acturelli) ^ ":\n");  *)

          let spec = findCallSpecFrom env calleeName in 
          match spec with
          | None -> ([], currentreachableState)
          | Some ((signiture, formalLi), factSchema)-> 
            let facts = 
              if List.length acturelli == List.length formalLi then 
                let insRet = 
                  match !handlerVar with 
                  | None -> [] 
                  | Some handler -> 
                    let () = varSet := !varSet @ [handler] in 
                    [(handler, BRET)]
                in 
                let vb = var_binding formalLi acturelli in 
                (instantiateFacts factSchema (vb @ insRet))
              (* facts instantiation *)
              else factSchema
            in 
            let callFacts = List.map facts ~f:(fun (str, args) -> (str, args@[(BINT fp)])) in 
            let flowfact = List.map currentreachableState ~f:(fun a -> ("flow", [BINT a; BINT fp])) in 
            (callFacts @ flowfact, [fp])
        )
    in [(currentfacts @ facts, 0, nextRechable)]
*)
  
  | IfStmt (stmt_info, conditional::branches, if_stmt_info) -> 
    let (fp, _) = stmt_intfor2FootPrint stmt_info in 
    let fp = (int_of_intList fp) in 

    let (prorgamStateThen, programStateElse) = 
      match stmt2Pure conditional with 
      | None -> (current, current)
      | Some piCondition -> 
        (match findIfStmtSpecFrom env piCondition with 
        | None -> (current, current) 
        | Some (vb, factSchema:: rest) -> 
          let flowfact = List.map currentreachableState ~f:(fun a -> ("flow", [BINT a; BINT fp])) in 

          let rawFactsThen = instantiateFacts [factSchema] vb in 
          let factsThenWithLineNo = List.map rawFactsThen ~f:(fun (str, args) -> (str, args@[(BINT fp)])) in 

          let prorgamStateThen' = (currentfacts @ factsThenWithLineNo @ flowfact, 0, [fp]) in 
          let programStateElse' = 
            match rest with 
            | [] -> current 
            | thenFactSchema :: _ -> 
              (*print_endline ("second tempate for ifelse" ^ string_of_fact thenFactSchema); *)
              let rawFactsElse = instantiateFacts [thenFactSchema] vb in 
              let factsElseWithLineNo = List.map rawFactsElse ~f:(fun (str, args) -> (str, args@[(BINT fp)])) in 
              (factsElseWithLineNo, 0, [fp])
          in (prorgamStateThen', current (*programStateElse'*))
        | _ -> raise(Failure "IfStmt spec no facts ") 
        )
    in 

    (match branches with 
      | [thenBranch] -> 
        let programStatesThen = syh_compute_stmt_facts prorgamStateThen env thenBranch in  
        programStateElse :: programStatesThen
      | [thenBranch; elseBranch] -> 
        let programStatesThen = syh_compute_stmt_facts prorgamStateThen env thenBranch in  
        let programStatesElse = syh_compute_stmt_facts programStateElse env elseBranch in  
        programStatesThen @ programStatesElse 
      | _ -> raise(Failure "IfStmt has more than 2 branches") 
    ) 
    


  | ReturnStmt _ -> [(currentfacts, 1, currentreachableState)]
  | ImplicitCastExpr (_, x::_, _, _, _) 
  | DeclStmt (_, [x], _) -> syh_compute_stmt_facts current env x
  | ImplicitCastExpr _ 
  | StringLiteral _ 
  | BinaryOperator _  
  | DeclStmt _ -> (* mute *) [current]
  | _ -> print_endline ("Facts to be generated for " ^ ": "^ (Clang_ast_proj.get_stmt_kind_string instr)); 
         [current] 


  (*
  | ReturnStmt (stmt_info, [ret]) ->
    (*print_endline ("ReturnStmt1:" ^ string_of_stmt_list [ret] " ");*)

    let (fp, _) = stmt_intfor2FootPrint stmt_info in 
    let fp1 = match fp with | [] -> None | x::_ -> Some x in 

    let optionTermToList inp = 
      match inp  with 
      | Some (Basic (BVAR t)) -> [(BVAR t)] 
      | _ -> [] 
    in 

    let (extrapure, es) = match ret with
    | CallExpr (stmt_info, _::stmt_list, ei) ->
      let arg = List.fold_left stmt_list ~init:[] ~f:(fun acc a -> acc @(optionTermToList (stmt2Term a))) in 
      let es  = Singleton (("RET", arg), fp1) in 
      (Ast_utility.TRUE, es)
    | _ -> 
    let retTerm = stmt2Term ret in 
    let extrapure = 
      match retTerm with 
      | Some (Basic (BINT n)) -> Eq(Basic(BRET), Basic(BINT n))
      | Some (Basic (BVAR str)) -> Eq(Basic(BRET), Basic(BVAR str))
      | _ -> Ast_utility.TRUE
    in 
    let retTerm1 = optionTermToList retTerm in 
    let es = if List.length (retTerm1 ) ==0 then Emp else Singleton (("RET", (retTerm1)), fp1) in 
    (extrapure, es)

    in 
    [(extrapure, es, 1, fp)]
  
  | ReturnStmt (stmt_info, stmt_list) ->
    (*print_endline ("ReturnStmt:" ^ string_of_stmt_list stmt_list " ");*)
    let (fp, _) = stmt_intfor2FootPrint stmt_info in 
    [(Ast_utility.TRUE, Emp, 1, fp)]
  

  | ForStmt (stmt_info, stmt_list)



  

  | MemberExpr (stmt_info, x::_, _, _) -> 
    let (fp, _) =  getStmtlocation instr in 
    let ev = Singleton ((("deref", [(BVAR(string_of_stmt x))])), fp) in 
    let () = dynamicSpec := ((string_of_stmt instr, []), None, Some [(TRUE, ev )], None) :: !dynamicSpec in 

    let fp = match fp with | None -> [] | Some l -> [l] in 
    [(TRUE, ev, 0, fp)]


  | UnaryOperator _ (*stmt_info, stmt_list, _, _*)   
  | BinaryOperator _ 
  | MemberExpr _
  | NullStmt _
  | CharacterLiteral _ 
  | FixedPointLiteral _ 
  | FloatingLiteral _ 
  | IntegerLiteral _ 
  | StringLiteral _ 
  | RecoveryExpr _ 
  | DeclRefExpr _  
  | DeclStmt (_, [], _) 
  | WhileStmt _ 
  | SwitchStmt _ 
  | ParenExpr _ (* assert(max > min); *)
  (*| ForStmt _ *)
  | CallExpr _ (* nested calls:  if (swoole_timer_is_available()) {    *)
  | CXXOperatorCallExpr _ 
  | CXXDeleteExpr _ (* delete g_logger_instance; *)
  (*| CStyleCastExpr _ *) (*  char *buf = (char * ) sw_malloc(n); *)
  | ExprWithCleanups _ (* *value = std::stoi(e);  *)
  | CXXConstructExpr _ (* va_list args; *)
  | CompoundAssignOperator _  (* retval += sw_snprintf(sw ...*)
  | CXXMemberCallExpr _ (* sw_logger()->put *)
  | CXXConstructExpr _ (* va_list va_list; *)
  | DoStmt _ ->
    
    let (fp, _) = maybeIntToListInt (getStmtlocation instr) in 
    [(TRUE, Emp, 0, fp)]

  | DeclStmt (_, stmt_list, _) -> 
    let (fp, fp1) =  (getStmtlocation instr) in 


    let ev = Singleton (((Clang_ast_proj.get_stmt_kind_string instr ^ " " ^ string_of_int (List.length stmt_list), [])), fp) in 
    let () = dynamicSpec := ((string_of_stmt instr, []), None, Some [(TRUE, ev )], None) :: !dynamicSpec in 

    let (fp, _) = maybeIntToListInt (fp, fp1) in 
    [(TRUE, ev, 0, fp)]


  | ContinueStmt _
  | BreakStmt _
  | ParenExpr _
  | ArraySubscriptExpr _
  | UnaryExprOrTypeTraitExpr _
  | CStyleCastExpr _ 
  | _ -> 
    let (fp, fp1) =  (getStmtlocation instr) in 

    let ev = Singleton ((Clang_ast_proj.get_stmt_kind_string instr, []), fp) in 
    let () = dynamicSpec := ((string_of_stmt instr, []), None, Some [(TRUE, ev )], None) :: !dynamicSpec in 

    let (fp, _) = maybeIntToListInt (fp, fp1) in 


    [(TRUE, ev, 0, fp)]
    *)



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
      (if List.length partitions == 0 then ()
      else print_endline ("Global specifictaions are: "));
      let sepcifications = List.map partitions 
        ~f:(fun singlespec -> 
          (*print_endline (singlespec);*)
          Parser.ctl Lexer.token (Lexing.from_string singlespec)) in
      
      
      let _ = List.map sepcifications ~f:(fun ctl -> print_endline (string_of_ctl ctl) ) in 
      

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


let removeRedundantFlows factList : facts = 
  let getTuple4Flows = 
    List.fold_left factList ~init:[] ~f:(fun acc (_, args) -> 
      match args with 
      | [BINT i1; BINT i2] -> acc @ [(i1, i2)]
      | _ -> acc) 
  in 
  let rec existSameRecord recordList start endNum  : bool = 
    match recordList with 
    | [] -> false 
    | (s',e'):: recordListxs -> if start ==s' && endNum==e' then true else existSameRecord recordListxs start endNum
  in 

  let rec helper tupleList = 
    match tupleList with 
    | [] -> []
    | [x] -> [x]
    | (i1, i2)::rest -> 
      if existSameRecord rest i1 i2 then helper rest 
      else (i1, i2)::helper rest 
  in 
  List.map (helper getTuple4Flows) ~f:(fun (i1, i2) -> ("flow", [BINT i1; BINT i2]))


let reason_about_declaration (dec: Clang_ast_t.decl) (specifications: specification list) (source_Address:string): unit  = 
  match dec with
    | FunctionDecl (decl_info, named_decl_info, _, function_decl_info) ->
      let source_Addressnow = string_of_source_range  decl_info.di_source_range in 
      if String.compare source_Address source_Addressnow !=0 then ()
      else 
      let (l1, l2) = decl_info.di_source_range in 
      let (functionStart, functionEnd) = (int_of_optionint (l1.sl_line), int_of_optionint (l2.sl_line)) in 
      let () = currentFunctionLineNumber := (functionStart, functionEnd) in 
      (
      match function_decl_info.fdi_body with 
      | None -> ()
      | Some stmt -> 
      let funcName = named_decl_info.ni_name in 
      let () = varSet := [] in 

      print_endline ("//<<=== Facts for function: "^ funcName ^" ===>>\n" ); 
      (* initial states are facts = [] , exit code = 0, rechableState = [] *)
      let prorgamStates = (syh_compute_stmt_facts ([], 0, [functionStart]) specifications stmt) in 
      let factsFromProgram = List.fold_left prorgamStates ~init:[] ~f:(fun acc (fs, _, _) -> acc @ fs) in 
      let facts = ("Entry", [(BINT functionStart)]) :: factsFromProgram in 
      let (entryFacts, flowFacts, restFacts) = 
        List.fold_left facts
        ~init:([], [], [])
        ~f:
        (fun (entryFacts', flowFacts', restFacts') a ->
          let (str, args) = a in 
          if String.compare "Entry" str == 0 then (entryFacts'@[a], flowFacts', restFacts')
          else if String.compare "flow" str == 0 then (entryFacts', flowFacts'@[a], restFacts')
          else (entryFacts', flowFacts', restFacts'@[a])
        ) 
      in 
      let facts' = entryFacts @ (removeRedundantFlows flowFacts) @ restFacts in 
      print_endline (string_of_facts facts' ^ "\n")
      )
    | _ -> () 

let retrive_basic_info_from_AST ast_decl: (string * Clang_ast_t.decl list * ctl list * int * int * int) = 
    match ast_decl with
    | Clang_ast_t.TranslationUnitDecl (decl_info, decl_list, _, translation_unit_decl_info) ->
        let source =  translation_unit_decl_info.tudi_input_path in 
        let (specifications, lines_of_code, lines_of_spec, number_of_protocol) = retriveSpecifications source in 
        (source, decl_list, specifications, lines_of_code, lines_of_spec, number_of_protocol)
 
    | _ -> assert false

let do_source_file (translation_unit_context : CFrontend_config.translation_unit_context) ast =
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
                
  
  
  (*L.(debug Capture Verbose)
    "@\n Start building call/cfg graph for '%a'....@\n" SourceFile.pp source_file ;
  let cfg = compute_icfg translation_unit_context tenv ast in

  (*print_string("<<<SYH:Finished creating icfg>>>\n");*)


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
  *)
  
  ()
