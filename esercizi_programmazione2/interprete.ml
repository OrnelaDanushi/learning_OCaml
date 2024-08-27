(* http://caml.inria.fr/pub/docs/manual-ocaml-4.00/manual023.html  *)

type variable = string ;;

type constant = Int of int | Bool of bool ;;

type operand = Plus | Minus | Times | Div | LessThan | LessThanEq | MoreThan | MoreThanEq ;;

type exp = 						(* espressioni *)
  | Constant_e of constant
  | Op_e of exp * operand * exp
  | Var_e of variable
  | If_e of exp * exp * exp
  | Fun_e of variable * exp
  | FunCall_e of exp * exp
  | Let_e of variable * exp * exp
  | Letrec_e of variable * exp * exp ;;

(* Funzioni del run-time *)

exception UnboundVariable of variable ;;		(* casi possibili di runtime exception *)
exception BadApplication of exp ;;
exception BadIf of exp ;;
exception BadOp of exp * operand * exp ;;

let eval_op (v1:exp) (op:operand) (v2:exp) : exp = 	(* decodifica delle operazioni di base *)
  match v1, op, v2 with 
    | Constant_e (Int i), Plus, Constant_e (Int j) ->		Constant_e (Int (i+j))
    | Constant_e (Int i), Minus, Constant_e (Int j) ->  	Constant_e (Int (i-j))
    | Constant_e (Int i), Times, Constant_e (Int j) ->  	Constant_e (Int (i*j))
    | Constant_e (Int i), Div, Constant_e (Int j) ->    	Constant_e (Int (i/j))
    | Constant_e (Int i), LessThan, Constant_e (Int j) ->	Constant_e (Bool (i<j))
    | Constant_e (Int i), LessThanEq, Constant_e (Int j) ->     Constant_e (Bool (i<=j))
    | Constant_e (Int i), MoreThan, Constant_e (Int j) -> 	Constant_e (Bool (i>j))
    | Constant_e (Int i), MoreThanEq, Constant_e (Int j) ->     Constant_e (Bool (i>=j))
    | _, _, _ -> raise (BadOp (v1,op,v2)) ;;

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
    | Letrec_e (x,e1,e2) -> 	(* Notare uso della sostituzione per fare unwind della ricorsione *)
        let e1_unwind = substitute (Letrec_e (x,e1,Var_e x)) x e1 in 
          eval (Let_e (x,e1_unwind,e2))
    | FunCall_e (e1,e2) ->
        match eval e1 with
           | Fun_e (x,e3) -> eval (substitute (eval e2) x e3)
           | v -> raise (BadApplication v)
;;

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
