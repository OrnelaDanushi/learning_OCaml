type variable = string ;;

type constant = Int of int | Bool of bool ;;

type operator = Plus | Minus | Times | Div | LessThan | LessThanEq ;;

(* Le espressioni *)

type exp =	Constant_e of constant	| Op_e of exp * operator * exp
 	| Var_e of variable			| If_e of exp * exp * exp
  	| Fun_e of variable * exp		| FunCall_e of exp * exp
  	| Let_e of variable * exp * exp		| Letrec_e of variable * exp * exp
;;

(* Funzioni del run-time *)

(* Controllo per valori *)

let rec is_value (e:exp) : bool = match e with 
    | Constant_e _ -> true
    | Fun_e (_,_) -> true
    | (Op_e(_,_,_) | Var_e _ | If_e(_,_,_)| FunCall_e(_,_) | Let_e(_,_,_)|Letrec_e(_,_,_))-> false
;;

(* casi possibili di run-time exception *)

exception UnboundVariable of variable ;;
exception BadApplication of exp ;;
exception BadIf of exp ;;
exception BadOp of exp * operator * exp ;;

(* Decodifica delle operazioni di base *)

let apply_op v1 op v2 =  match v1, op, v2 with 
	| Constant_e (Int i), Plus, Constant_e (Int j) -> 
        Constant_e (Int (i+j))
    | Constant_e (Int i), Minus, Constant_e (Int j) -> 
        Constant_e (Int (i-j))
    | Constant_e (Int i), Times, Constant_e (Int j) -> 
        Constant_e (Int (i*j))
    | Constant_e (Int i), Div, Constant_e (Int j) -> 
        Constant_e (Int (i/j))
    | Constant_e (Int i), LessThan, Constant_e (Int j) -> 
        Constant_e (Bool (i<j))
    | Constant_e (Int i), LessThanEq, Constant_e (Int j) -> 
        Constant_e (Bool (i<=j))
    | _, _, _ -> raise (BadOp (v1,op,v2))
;;

(* Funzione di sostituzione *)
(* Notare uso di una funzione ricorsiva ausiliaria *)

let substitute (v:exp) (x:variable) (e:exp) : exp = 
  let rec subst (e:exp) : exp = 
    match e with 
    | Var_e y -> if x = y then v else e
    | Constant_e _ -> e
    | Op_e (e1,op,e2) -> Op_e (subst e1,op,subst e2)
    | If_e (e1,e2,e3) -> If_e (subst e1,subst e2,subst e3)
    | FunCall_e (e1,e2) -> FunCall_e (subst e1,subst e2)
    | Fun_e (y,e1) -> if x = y then e else Fun_e (y, subst e1)
    | Let_e (y,e1,e2) -> 
        Let_e (y,subst e1,if x = y then e2 else subst e2)
    | Letrec_e (y,e1,e2) -> 
        if x = y then Letrec_e (y,e1,e2) else Letrec_e (y,subst e1,subst e2)
  in 
    subst e
;;

(* Ciclo dell'interprete *)
(* Notare uso di una chiamata ricorsiva tramite parametri higher-order *)
(* Notare uso della sostituzione per fare unwind della ricorsione *)

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

let rec eval e = eval_body eval e
;;


(* Test: il fattoriale *)

(* Body del fattoriale: fun n -> if n < 1 then 1 else n * fact (n - 1) *)
let fact_body = Fun_e ("n", 
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




Lezione 18: INTERPRETE RICORSIVO
(* Environment *)

let emptyenv = [] ;; (* the empty environment *)

let rec lookup env x = match env with 
    | []        -> failwith ("not found")
    | (y, v)::r -> if x = y then v else lookup r x 
;;

(* AST *)
type expr = 
  | CstI of int
  | Var of string
  | Let of string * expr * expr
  | Prim of string * expr * expr
;;

(* Interpreter *)
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

INTERPRETE RICORSIVO CON CODICE INTERMEDIO
(* AST *)
type expr =                        
  | CstI of int
  | Var of string
  | Let of string * expr * expr
  | Prim of string * expr * expr 
;;

type texpr =                  (* target expressions *)
  | TCstI of int
  | TVar of int               (* index into runtime environment *)
  | TLet of texpr * texpr     (* erhs and ebody *)
  | TPrim of string * texpr * texpr 
;;

(* index computation *)
let rec getindex env x = match env with 
    | [] -> failwith("Variable not found")
    | y::yr -> if x=y then 0 else 1 + getindex yr x 
;;

(* IR Optimization *)
let rec tcomp e (cenv : string list) : texpr = match e with
      | CstI i -> TCstI i
      | Var x  -> TVar (getindex cenv x)
      | Let(x, erhs, ebody) -> 
            let cenv1 = x :: cenv in
              TLet(tcomp erhs cenv, tcomp ebody cenv1)
      | Prim(ope, e1, e2) -> TPrim(ope, tcomp e1 cenv, tcomp e2 cenv) 
;;

(* Interpreter  *)
(* Environment list of integers *)
open List ;;
let rec teval (e : texpr) (renv : int list) : int =match e with
      | TCstI i -> i
      | TVar x  -> nth renv x
      | TLet(erhs, ebody) -> 
            let xval = teval erhs renv in
               let renv1 = xval :: renv  in
                  teval ebody renv1
      | TPrim("+", e1, e2) -> teval e1 renv + teval e2 renv
      | TPrim("*", e1, e2) -> teval e1 renv * teval e2 renv
      | TPrim("-", e1, e2) -> teval e1 renv - teval e2 renv
      | TPrim _            -> failwith("unknown primitive") 
;;

let e2 = Let("z", CstI 17, Prim("+", Let("z", CstI 22, Prim("*", CstI 100, Var "z")), Var "z")) ;;

(* Correctness: eval e [] equals teval (tcomp e []) [] *)

