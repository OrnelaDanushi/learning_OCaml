(* http://caml.inria.fr/pub/docs/manual-ocaml-4.00/manual023.html  *)

type variable = string ;;

type constant = Int of int | Bool of bool ;;

type operand = Plus | Minus | Times | Div | LessThan | LessThanEq | MoreThan | MoreThanEq ;;


(* Environment *)

let emptyenv = [] ;; (* empty environment *)

let rec lookup env x = match env with 
    | []        -> failwith ("not found")
    | (y, v)::r -> if x = y then v else lookup r x 
;;

type exp = 						                              (* espressioni *)
  | Constant_e of constant
  | Var_e of variable
  | Op_e of exp * operand * exp
  | If_e of exp * exp * exp
  | Fun_e of variable * exp
  | FunCall_e of exp * exp
  | Let_e of variable * exp * exp
  | Letrec_e of variable * exp * exp ;;

(*

(* interprete con codice intermedio ----------------------------------------- *)

let rec getindex (env : variable list)(x : variable) : int = match env with     (* Calcolo dell'indice *)
    	| [] -> failwith("Variable not found")
    	| y::yr -> if x=y then 0 else 1 + getindex yr x 
;;

type expr =                                         (* AST *)
  | CstI of int
  | Var of string
  | Let of string * expr * expr
  | Prim of string * expr * expr
;;

type texpr =                                          (* espressioni target *)
  | TCstI of int
  | TVar of int                                       (* indice dell'ambiente a runtime *)
  (* | TOp of texpr * operand * texpr   *)
  | TLet of texpr * texpr                             (* erhs and ebody *)
  | TPrim of string * texpr * texpr 
;;

let rec tcomp (e:expr) (cenv : string list) : texpr = match e with          (* IR Optimization *)
      | CstI i -> TCstI i
      | Var x  -> TVar (getindex cenv x)
      | Let(x, erhs, ebody) -> 
            let cenv1 = x :: cenv in
              TLet(tcomp erhs cenv, tcomp ebody cenv1)
      | Prim(ope, e1, e2) -> TPrim(ope, tcomp e1 cenv, tcomp e2 cenv) 
;;
(* ----------------------------------------------------------------------- *)

*)

let rec is_value (e:exp) : bool = match e with     (* controllo per valori *)
    | Constant_e _ -> true
    | Fun_e (_,_) -> true
    | (Op_e(_,_,_) | Var_e _ | If_e(_,_,_)| FunCall_e(_,_) | Let_e(_,_,_)|Letrec_e(_,_,_)) -> false ;;


(* Funzioni del run-time *)

exception UnboundVariable of variable ;;		(* casi possibili di runtime exception *)
exception BadApplication of exp ;;
exception BadIf of exp ;;
exception BadOp of exp * operand * exp ;;

(* decodifica delle operazioni di base *)
let eval_op (v1:exp) (op:operand) (v2:exp) : exp = match v1, op, v2 with 
    | Constant_e (Int i), Plus, Constant_e (Int j) ->		Constant_e (Int (i+j))
    | Constant_e (Int i), Minus, Constant_e (Int j) ->  	Constant_e (Int (i-j))
    | Constant_e (Int i), Times, Constant_e (Int j) ->  	Constant_e (Int (i*j))
    | Constant_e (Int i), Div, Constant_e (Int j) ->    	Constant_e (Int (i/j))
    | Constant_e (Int i), LessThan, Constant_e (Int j) ->	Constant_e (Bool (i<j))
    | Constant_e (Int i), LessThanEq, Constant_e (Int j) -> Constant_e (Bool (i<=j))
    | Constant_e (Int i), MoreThan, Constant_e (Int j) -> 	Constant_e (Bool (i>j))
    | Constant_e (Int i), MoreThanEq, Constant_e (Int j) -> Constant_e (Bool (i>=j))
    | _, _, _ -> raise (BadOp (v1,op,v2)) ;;

(* oppure
let eval_op (v1: int)(op: operand)(v2: int) : int = match v1, op, v2 with    
    | _, Plus, _ -> v1 + v2 
    | _, Minus, _ -> v1 - v2 
    | _, Times, _ -> v1 * v2 
    | _, Div, _ -> v1 / v2 
    | _, LessThan, _ -> v1 < v2 
    | _, LessThanEq, _ -> v1 <= v2 
    | _, MoreThan, _ -> v1 > v2 
    | _, MoreThanEq, _ -> v1 >= v2 
    | _, _, _ -> raise (BadOp (v1, op, v2)) ;;
*)

(* Funzione di sostituzione *)

let substitute (v:exp) (x:variable) (e:exp) : exp =  
  let rec subst (e:exp) : exp = 				(* notare uso di una funzione ricorsiva ausiliaria *)
    match e with 
      | Var_e y -> if x = y then v else e
      | Constant_e _ -> e
      | Op_e (e1,op,e2) -> Op_e (subst e1,op,subst e2)
      | If_e (e1,e2,e3) -> If_e (subst e1,subst e2,subst e3)
      | FunCall_e (e1,e2) -> FunCall_e (subst e1,subst e2)
      | Fun_e (y,e1) -> if x = y then e else Fun_e (y, subst e1)
      | Let_e (y,e1,e2) -> Let_e (y,subst e1,if x = y then e2 else subst e2)
      | Letrec_e (y,e1,e2) ->
          if x = y then Letrec_e (y,e1,e2)
          else Letrec_e (y,subst e1,subst e2)
  in subst e ;;

(* Ciclo dell'interprete *)

let rec eval (e:exp) : exp =
  match e with
    | Constant_e _ -> e
    | Fun_e _ -> e
    | Op_e (e1,op,e2) -> 
        let v1 = eval e1 in
          let v2 = eval e2 in
            eval_op v1 op v2
    | If_e (e1,e2,e3) ->
        (match eval e1 with
         | Constant_e (Bool true) -> eval e2
         | Constant_e (Bool false) -> eval e3
         | v1 -> raise (BadIf v1))
    | Let_e (x,e1,e2) -> eval (substitute (eval e1) x e2)
    | Var_e x -> raise (UnboundVariable x)
    | Letrec_e (x,e1,e2) -> 	(* sostituzione per fare unwind della ricorsione *)
        let e1_unwind = substitute (Letrec_e (x,e1,Var_e x)) x e1 in 
          eval (Let_e (x,e1_unwind,e2))
    | FunCall_e (e1,e2) ->
        match eval e1 with
           | Fun_e (x,e3) -> eval (substitute (eval e2) x e3)
           | v -> raise (BadApplication v)
;;

(* oppure *)

let eval_body (eval_loop:exp->exp) (e:exp) : exp = 
  match e with
    | Constant_e c -> Constant_e c 
    | Fun_e (x,e) -> Fun_e (x,e)
    | Op_e (e1,op,e2) -> 
        let v1 = eval_loop e1 in 
          let v2 = eval_loop e2 in 
            apply_op v1 op v2 
    | If_e (e1,e2,e3) -> 
          match eval_loop e1 with 
             | Constant_e (Bool true) -> eval_loop e2
             | Constant_e (Bool false) -> eval_loop e3
             | v1 -> raise (BadIf v1)
    | Let_e (x,e1,e2) -> eval_loop (substitute (eval_loop e1) x e2)
    | FunCall_e (e1,e2) -> 
        match eval_loop e1 with 
           | Fun_e (x,e) -> eval_loop (substitute (eval_loop e2) x e)
           | v1 -> raise (BadApplication v1)
    | Var_e x -> raise (UnboundVariable x)
    | Letrec_e (x,e1,e2) -> 
        let e1_unwind = substitute (Letrec_e (x,e1,Var_e x)) x e1 in 
          eval_loop (Let_e (x,e1_unwind,e2))
;;     

let rec eval2 e = eval_body eval2 e ;; (* chiamata ricorsiva tramite parametri higher-order *)

(* 

(* ciclo dell'interprete ricorsivo *)
let rec eval (e : expr) (env : (string * int) list) : int =match e with
      | CstI i -> i
      | Var x  -> lookup env x 
      | Let(x, erhs, ebody) -> 
            let xval = eval erhs env in
              let env1 = (x, xval) :: env in
                eval ebody env1
      | Prim("+", e1, e2) -> eval e1 env + eval e2 env
      | Prim("*", e1, e2) -> eval e1 env * eval e2 env
      | Prim("-", e1, e2) -> eval e1 env - eval e2 env
      | Prim _            -> raise (Failure "unknown primitive") 
;;

let run e = eval e [] ;;

*)

(* Test: il fattoriale *)

(* Body del fattoriale: fun n -> if n < 1 then 1 else n * fact (n - 1) *)
let fact_body =
   Fun_e ("n",
          If_e (Op_e (Var_e "n", LessThan, Constant_e (Int 1)),
                Constant_e (Int 1),
                Op_e (Var_e "n", Times,
                      FunCall_e (Var_e "fact",
                                 Op_e (Var_e "n", Minus,
                                       Constant_e (Int 1))))))
;;

(* Chiamata: fact 4 *)
let fact_call = FunCall_e (Var_e "fact", (Constant_e (Int 4))) ;;

(* Definizione ricorsiva del fattoriale chiamato sul valore 4 *)
let fact4 = Letrec_e ("fact", fact_body, fact_call) ;;

(* Chiamata interprete *)
eval fact4 ;;

(* Risultato: - : exp = Constant_e (Int 24) *)

(* 

(* Ciclo dell'interprete *)
open List ;;

let rec teval (e : texpr) (renv : int list) : int = match e with      (* Environment list of integers *)
      | TCstI i -> i
      | TVar x  -> nth renv x                                         (*oppure List.nth renv x *)
      | TLet(erhs, ebody) -> 
            let xval = teval erhs renv in
               let renv1 = xval :: renv  in
                  teval ebody renv1

      (* oppure 
      | TOp (e1, op, e2) -> let v1 = teval e1 renv in let v2 = teval e2 renv in eval_op v1 op v2 
      senza dover riscrivere tutte le operazioni previste da operand come è stato fatto invece di seguito
      *)
      | TPrim("+", e1, e2) -> teval e1 renv + teval e2 renv
      | TPrim("*", e1, e2) -> teval e1 renv * teval e2 renv
      | TPrim("-", e1, e2) -> teval e1 renv - teval e2 renv
      | TPrim _            -> failwith("unknown primitive") 
;;

let e2 = Let("z", CstI 17, Prim("+", Let("z", CstI 22, Prim("*", CstI 100, Var "z")), Var "z")) ;;
(* let expEx = Let("z", Cnst 17, Op(Let("z", Cnst 22, Op(Cnst 100, Times, Var "z")), Plus, Var "z")) ;; *)


(* Correctness: eval e [] equals teval (tcomp e []) [] *)

*)

