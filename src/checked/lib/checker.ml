open ReM
open Dst
open Parser_plaf.Ast
open Parser_plaf.Parser
       
let rec chk_expr : expr -> texpr tea_result = function 
  | Int _n -> return IntType
  | Var id -> apply_tenv id
  | IsZero(e) ->
    chk_expr e >>= fun t ->
    if t=IntType
    then return BoolType
    else error "isZero: expected argument of type int"
  | Add(e1,e2) | Sub(e1,e2) | Mul(e1,e2)| Div(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    if (t1=IntType && t2=IntType)
    then return IntType
    else error "arith: arguments must be ints"
  | ITE(e1,e2,e3) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    chk_expr e3 >>= fun t3 ->
    if (t1=BoolType && t2=t3)
    then return t2
    else error "ITE: condition not boolean or types of then and else do not match"
  | Let(id,e,body) ->
    chk_expr e >>= fun t ->
    extend_tenv id t >>+
    chk_expr body
  | Proc(var,Some t1,e) ->
    extend_tenv var t1 >>+
    chk_expr e >>= fun t2 ->
    return @@ FuncType(t1,t2)
  | Proc(_var,None,_e) ->
    error "proc: type declaration missing"
  | App(e1,e2) ->
    chk_expr e1 >>=
    pair_of_funcType "app: " >>= fun (t1,t2) ->
    chk_expr e2 >>= fun t3 ->
    if t1=t3
    then return t2
    else error "app: type of argument incorrect"
  | Letrec([(_id,_param,None,_,_body)],_target) | Letrec([(_id,_param,_,None,_body)],_target) ->
    error "letrec: type declaration missing"
  | Letrec([(id,param,Some tParam,Some tRes,body)],target) ->
    extend_tenv id (FuncType(tParam,tRes)) >>+
    (extend_tenv param tParam >>+
     chk_expr body >>= fun t ->
     if t=tRes 
     then chk_expr target
     else error
         "LetRec: Type of recursive function does not match
declaration")
  | NewRef(e) -> 
    chk_expr e >>= fun t ->
    return (RefType (t))
  | DeRef(e) -> 
    chk_expr e >>= fun t ->
    (match t with
    | RefType(t1) -> return t1
    | _ -> error "DeRef: argument must be a reference")
  | SetRef(e1,e2) -> 
    chk_expr e1 >>= fun t1 ->
    (match t1 with
    | RefType(t) -> 
        chk_expr e2 >>= fun t2 ->
        if t=t2
          then 
            return UnitType 
        else 
          error "setref: type mismatch"
    | _ -> error "setref: Expected a reference type")
  | BeginEnd([]) -> return UnitType
  | BeginEnd(es) -> 
    List.fold_left (fun c e -> c >>= fun _ -> chk_expr e) (return UnitType) es (* From previous implementations of BeginEnd in explicit-refs *)
  | EmptyList(t) -> 
    (match t with
    | Some t1 -> return (ListType(t1))
    | None -> error "EmptyList: type declaration missing"
    )
  | Cons(e1, e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    (match t2 with
    | ListType (t) -> 
        if t=t1 
          then 
            return t2 
        else 
          error "cons: type of head and tail do not match"
    | _ -> error "cons: second argument must be a list")
  | IsEmpty(e) -> 
    chk_expr e >>= fun t ->
    (match t with
    | ListType (_) | TreeType(_) -> return BoolType 
    | _ -> error "isEmpty: argument must be a list")
  | Hd(e) -> 
    chk_expr e >>= fun t ->
    (match t with
    | ListType(t1) -> return t1
    | _ -> error "hd: argument must be a list")
  | Tl(e) -> 
    chk_expr e >>= fun t ->
    (match t with
    | ListType(_) -> return t
    | _ -> error "tl: argument must be a list")
  | EmptyTree(t) -> 
    (match t with
    | Some t1 -> return (TreeType(t1))
    | None -> error "EmptyTree: Cannot create empty tree without type declaration"
    )
  | Node(de, le, re) -> 
    chk_expr de >>= fun t1 ->
    chk_expr le >>= fun t2 ->
    chk_expr re >>= fun t3 ->
    (match t2, t3 with
    | TreeType(t2), TreeType(t3) -> 
        if t1=t2 && t1=t3 
          then 
            return (TreeType(t1)) 
        else 
          error "node: type mismatch"
    | _ -> error "node: arguments must be trees")
  | CaseT(target, emptycase, id1, id2, id3, nodecase) ->
    chk_expr target >>= fun t ->
    (match t with
    | TreeType(t1) -> 
        chk_expr emptycase >>= fun t2 ->
          if (t1=t2) 
            then
              extend_tenv id1 t1 >>+
              extend_tenv id2 (TreeType(t1)) >>+
              extend_tenv id3 (TreeType(t1)) >>+
              chk_expr nodecase
          else 
            chk_expr emptycase
    | _ -> error "caseT: target must be a tree")
  | Debug(_e) ->
    string_of_tenv >>= fun str ->
    print_endline str;
    error "Debug: reached breakpoint"
  | _ -> failwith "chk_expr: implement"    
and
  chk_prog (AProg(_,e)) =
  chk_expr e

(* Type-check an expression *)
let chk (e:string) : texpr result =
  let c = e |> parse |> chk_prog
  in run_teac c

let chkpp (e:string) : string result =
  let c = e |> parse |> chk_prog
  in run_teac (c >>= fun t -> return @@ string_of_texpr t)



