(* Interprete di un semplice linguaggio funzionale con ambiente *)
(* Evaluating simple expressions with variables *)

type variable = string ;;

type constant = int ;;

type operand = Plus | Minus | Times | Div ;;

(* Le espressioni *)
(* Object language expressions with variables *)

type exp =	Cnst of constant	| Var of variable
  | Op of exp * operand * exp		| Let of variable * exp * exp
;;



(* Association lists map object language variables to their values *)

let env = [("a", 3); ("c", 78); ("baf", 666); ("b", 111)];;

(* Funzioni del run-time *)

(* Environment *)

let emptyenv = [] ;; (* the empty environment *)

let rec lookup env x = match env with 
    | []        -> failwith("Variable not found")
    | (y, v)::t -> if x = y then v else lookup t x 
;;


let value1 = lookup env "a";;
let value2 = lookup env "c";;
let value3 = lookup env "baf";;
let value4 = lookup env "b";;


(* Decodifica delle operazioni di base *)

let eval_op (v1 : int) (op : operand) (v2 : int) : int = match v1, op, v2 with 
    | _, Plus, _ -> v1 + v2 
    | _, Minus, _ -> v1 - v2 
    | _, Times, _ -> v1 * v2 
    | _, Div, _ -> v1 / v2 
;;
(* Evaluation within an environment *)
(* Ciclo dell'interprete *)

let rec eval (e : exp) (env : (variable * int) list) : int = match e with
    | Cnst i -> i
    | Var x  -> lookup env x 
    | Op (e1, op, e2) -> 
        let v1 = eval e1 env in
          let v2 = eval e2 env in
            eval_op v1 op v2
    | Let (x, erhs, ebody) ->           
        let xval = eval erhs env in
              let env1 = (x, xval) :: env in
                eval ebody env1
;;

let run e = eval e [] ;;

let e1 = Cnst 17;;
let evale1 = eval e1 env ;;

let ea = Op( Cnst 3, Plus, Var "a");;
let va = eval ea env ;;		(* int 6 *)
let ec = Op( Cnst 3, Times, Var "c");;
let vc = eval ec env ;;		(* int 234 *)
(* … *)

let e3 = Op(Cnst 3, Plus, Cnst 4);;
let evale3 = eval e3 env ;;	(* int 7 *)
	
let e4 = Op(Op(Var "b", Times, Cnst 9), Plus, Var "a");;
let evale4 = eval e4 env ;;	(* int 1002 *)
