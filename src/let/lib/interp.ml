open Parser_plaf.Ast
open Parser_plaf.Parser
open Ds
    
(** [eval_expr e] evaluates expression [e] *)
let rec eval_expr : expr -> exp_val ea_result =
  fun e ->
  match e with
  | Int(n) ->
    return (NumVal n)
  | Var(id) ->
    apply_env id
  | Add(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1+n2))
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1-n2))
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1*n2))
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return (NumVal (n1/n2))
  | Let(id,def,body) ->
    eval_expr def >>= 
    extend_env id >>+
    eval_expr body 
  | ITE(e1,e2,e3) ->
    eval_expr e1 >>=
    bool_of_boolVal >>= fun b ->
    if b 
    then eval_expr e2
    else eval_expr e3
  | IsZero(e) ->
    eval_expr e >>=
    int_of_numVal >>= fun n ->
    return (BoolVal (n = 0))
  | Pair(e1,e2) ->
    eval_expr e1 >>= fun ev1 ->
    eval_expr e2 >>= fun ev2 ->
    return (PairVal(ev1,ev2))
  | Fst(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (l,_) ->
    return l
  | Snd(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (_,r) ->
    return r
  | Cons(e1, e2) -> 
    eval_expr e1 >>=
    fun ev1 ->
    eval_expr e2 >>=
    list_of_listVal >>= fun ev2 ->
    return (ListVal (ev1::ev2))
  | Hd(e) -> eval_expr e >>=
    list_of_listVal >>= fun l ->
      if List.length l = 0
        then error "hd: List is empty"
      else return (List.hd l)
  | Tl(e) -> eval_expr e >>=
    list_of_listVal >>= fun l ->
      if List.length l = 0
        then error "tl: List is empty"
      else return (ListVal (List.tl l))
  | IsEmpty(e) -> eval_expr e >>=
    list_of_listVal >>= fun l ->
      return (BoolVal (List.length l = 0))
  | EmptyList(_) -> return (ListVal [])
  | Unpair(id1, id2, e1, e2) ->
    eval_expr e1 >>= 
    pair_of_pairVal >>= fun (l, r) ->
    extend_env id1 l >>+
    extend_env id2 r >>+
    eval_expr e2   
  | Tuple(es) -> 
    eval_exprs es >>= fun l ->
    return (TupleVal l)
  | Untuple(ids, e1, e2) -> 
    eval_expr e1 >>=
    list_of_tupleVal >>= fun l ->
    if List.length ids = List.length l
    then extend_env
      (List.hd ids) (List.hd l) >>+
      extend_env
      (List.hd (List.tl ids)) (List.hd (List.tl l)) >>+
      eval_expr e2
    else error "extend_env_list: Arguments do not match parameters!"
  | Debug(_e) ->
    string_of_env >>= fun str ->
    print_endline str; 
    error "Debug called"
  | _ -> failwith "Not implemented yet!"
and
  eval_exprs : expr list -> (exp_val list) ea_result = fun es ->
    match es with
    | [] -> return []
    | h::t -> eval_expr h >>= fun i -> eval_exprs t >>= fun l ->
    return (i::l)


(** [eval_prog e] evaluates program [e] *)
let eval_prog (AProg(_,e)) =
  eval_expr e

(** [interp s] parses [s] and then evaluates it *)
let interp (e:string) : exp_val result =
  let c = e |> parse |> eval_prog
  in run c
  


