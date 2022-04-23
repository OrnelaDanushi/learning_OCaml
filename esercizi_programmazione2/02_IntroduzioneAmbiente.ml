(* Interprete di un semplice linguaggio funzionale con ambiente e compilazione in codice intermedio *)

type variable = string ;;

type constant = int ;;

type operand = Plus | Minus | Times | Div ;;

(* Le espressioni *)

type exp =	Cnst of constant	| Var of variable
  | Op of exp * operand * exp		| Let of variable * exp * exp
;;

(* Le espressioni target *)

type texp =	TCnst of constant	| TVar of int               (* indice dell'ambiente a runtime *)
  | TOp of texp * operand * texp	| TLet of texp * texp
;;

(* Calcolo dell'indice *)

let rec getindex (env : variable list)(x : variable) : int = match env with 
    	| [] -> failwith("Variable not found")
    	| y::yr -> if x=y then 0 else 1 + getindex yr x 
;;

(* IR optimization *)

let rec tcomp (e: exp)(cenv: variable list) : texp = match e with
      | Cnst i -> TCnst i
      | Var x  -> TVar (getindex cenv x)
      | Op (e1, op, e2) -> TOp(tcomp e1 cenv, op, tcomp e2 cenv) 
      | Let (x, erhs, ebody) -> 
            let cenv1 = x :: cenv in TLet(tcomp erhs cenv, tcomp ebody cenv1)
;;

(* Decodifica delle operazioni di base *)

let eval_op(v1: int)(op: operand)(v2: int) : int = match v1, op, v2 with 
    | _, Plus, _ -> v1 + v2 
    | _, Minus, _ -> v1 - v2 
    | _, Times, _ -> v1 * v2 
    | _, Div, _ -> v1 / v2 
;;

(* Ciclo dell'interprete *)
open List;;

let rec teval(e: texp)(renv : int list) : int = match e with
      | TCnst i -> i
      | TVar x  -> List.nth renv x
      | TOp (e1, op, e2) -> let v1 = teval e1 renv in let v2 = teval e2 renv in eval_op v1 op v2
      | TLet (erhs, ebody) -> let xval = teval erhs renv in let renv1 = xval :: renv  in
                  teval ebody renv1
;;

let expEx = Let("z", Cnst 17, Op(Let("z", Cnst 22, Op(Cnst 100, Times, Var "z")), Plus, Var "z")) ;;

(* Correctness: eval e [] equals teval (tcomp e []) [] *)



