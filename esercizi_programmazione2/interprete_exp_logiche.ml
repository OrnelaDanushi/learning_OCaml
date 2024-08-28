
type operand = Plus | Minus | Times | Div | LessThan | LessThanEq | MoreThan | MoreThanEq ;;

type exp = 						(* espressioni *)
  | Int_e of int
  | Bool_e of bool
  | Op_e of exp * operand * exp
  | Var_e of string
  | Minore of exp * exp
  | MinoreUguale of exp * exp
  | Maggiore of exp * exp
  | MaggioreUguale of exp * exp
  | Uguaglianza of exp * exp
  | IsZero of exp
  | If_e of exp * exp * exp				(* IfThenElse_e … *)
  | Fun_e of string * exp
  | FunCall_e of exp * exp
  | Let_e of string * exp * exp 			(* Modifica ambiente *)
  | Letrec_e of string * exp * exp
  | Fun of (string list) * exp				(* Astrazione di funzione *)
  | Appl of exp * (exp list)				(* Applicazione di funzione *)
  | Not_e of exp 
  | And_e of exp * exp
  | Or_e of exp * exp
  | Xor_e of exp * exp
  | Record of (string * exp) list
  | Select of exp * string
;;

(* Funzioni del run-time *)

exception UnboundVariable of string ;;			(* casi possibili di runtime exception *)
exception BadApplication of exp ;;
exception BadIf of exp ;;
exception BadOp of exp * operand * exp ;;

let eval_op (v1:exp) (op:operand) (v2:exp) : exp = match v1, op, v2 with  (* Decodifica delle operazioni di base *)
    | Int_e i, Plus, Int_e j -> Int_e (i+j)
    | Int_e i, Minus, Int_e j -> Int_e (i-j)
    | Int_e i, Times, Int_e j -> Int_e (i*j)
    | Int_e i, Div, Int_e j -> Int_e  (i/j)	
    | Int_e i, LessThan, Int_e j -> Bool_e (i<j) 
    | Int_e i, LessThanEq, Int_e j -> Bool_e (i<=j)
    | Int_e i, MoreThan, Int_e j -> Bool_e (i>j)
    | Int_e i, MoreThanEq, Int_e j -> Bool_e (i>=j)   
    | _, _, _ -> raise (BadOp (v1,op,v2)) ;;

(* TEST di alcune operazioni di base per ogni operando previsto*)
eval_op (Int_e 3)(Plus)(Int_e 4) ;;
eval_op (Int_e 3)(Minus)(Int_e 4) ;;
eval_op (Int_e 3)(Times)(Int_e 4) ;;
eval_op (Int_e 3)(Div)(Int_e 4) ;;
eval_op (Int_e 3)(LessThan)(Int_e 4) ;;
eval_op (Int_e 3)(LessThanEq)(Int_e 4) ;;
eval_op (Int_e 3)(MoreThan)(Int_e 4) ;;
eval_op (Int_e 3)(MoreThanEq)(Int_e 4) ;;
(* --- *)

let substitute (v:exp) (x:string) (e:exp) : exp =   			(* Funzione di sostituzione *)
  let rec subst (e:exp) : exp =  match e with 				(* uso di funzione ricorsiva ausiliaria *)
      | Var_e y -> if x = y then v else e
      | Int_e _ -> e
      | Bool_e _ -> e
      | Op_e (e1,op,e2) -> Op_e (subst e1,op,subst e2)
      | If_e (e1,e2,e3) -> If_e (subst e1,subst e2,subst e3)
      | Fun_e (y,e1) -> if x = y then e else Fun_e (y, subst e1)
      | FunCall_e (e1,e2) -> FunCall_e (subst e1,subst e2)
      | Let_e (y,e1,e2) -> Let_e (y,subst e1,if x = y then e2 else subst e2)
      | Letrec_e (y,e1,e2) -> if x = y then Letrec_e (y,e1,e2) else Letrec_e (y,subst e1,subst e2)
  in subst e
;;

let rec lookupRecord body s = (match body with				(* Funzione di scansione e ricerca dei tipi Record *)
	| [] -> failwith ("Not found")
	| ( ss,v )::t -> if s=ss then v else lookupRecord t s	)
;;

let rec evalRecord body = match body with				(* Funzione di valutazione dei tipi Record *)
	| []->[]
	| (s,e)::t -> (s, eval_op e)::evalRecord t
;;

let rec eval (e:exp) : exp = match e with				(* Ciclo dell'interprete *)
    | Var_e x -> raise (UnboundVariable x)
    | Int_e _ -> e
    | Bool_e _ -> e
    | Fun_e _ -> e
    | Op_e (e1,op,e2) -> 
    	let v1 = eval e1 in
     		let v2 = eval e2 in
        		eval_op v1 op v2
    | If_e (e1,e2,e3) -> (match eval e1 with
         | Bool_e true -> eval e2
         | Bool_e false -> eval e3
         | v1 -> raise (BadIf v1) )
    | FunCall_e (e1, e2) -> (match eval e1 with
           | Fun_e (x, e3) -> eval (substitute (eval e2) x e3)
           | v -> raise (BadApplication v) )
    | Let_e (x,e1,e2) -> eval (substitute (eval e1) x e2)
    | Letrec_e (x,e1,e2) -> 
    	let e1_unwind = substitute (Letrec_e (x,e1,Var_e x)) x e1 in 
          	eval (Let_e (x,e1_unwind,e2))
	      	(* uso della funzione di sostituzione per fare unwind della ricorsione *)
    (*
    | Record (body) -> Record (evalRecord body)
    | Select (e, s) -> ( match eval e with
	| Record (body) -> lookupRecord body s
	| _ -> raise TypeMismatch  )	
    *)
;;

let rec evalLogica (e:exp) :exp = match e with					(* Interprete di espressioni logiche *)
	| Bool_e true -> Bool_e true
	| Bool_e false -> Bool_e false
	| Not_e (e1) -> (match evalLogica e1 with
		| Bool_e true -> Bool_e false
		| Bool_e false -> Bool_e true )
	| And_e (e1, e2) -> (match (evalLogica e1, evalLogica e2) with
		| (Bool_e true, Bool_e true) -> Bool_e true	
		| (Bool_e false, _ ) -> Bool_e false
		| (_, Bool_e false ) -> Bool_e false	)
	| Or_e (e1, e2) -> (match (evalLogica e1, evalLogica e2) with
		| (Bool_e false, Bool_e false ) -> Bool_e false
		| (Bool_e false, Bool_e true) -> Bool_e true	
		| (Bool_e true, Bool_e false) -> Bool_e true	
		| (Bool_e true, Bool_e true ) -> Bool_e true	)
	| Xor_e (e1, e2) -> (match (evalLogica e1, evalLogica e2) with
		| (Bool_e false, Bool_e false ) -> Bool_e false
		| (Bool_e false, Bool_e true) -> Bool_e true	
		| (Bool_e true, Bool_e false) -> Bool_e true	
		| (Bool_e true, Bool_e true ) -> Bool_e false	)
;;


(* Interprete per espressioni intere con il loro ambiente *)

let emptyenv = [] ;;						(* ambiente vuoto *)

let rec lookup env x = match env with				(* scansiona la lista env fino a che non trova l’elemento x *)
	| [] -> failwith ("Not found")
	| (y, v)::r -> if x=y then v else lookup r x ;;

let rec evalamb (e:exp)(env:(string*int)list) :int = match e with
	| Var_e x -> lookup env x
    	| Int_e i -> i
	| Let_e (x, erhs, ebody) -> 
 		let xval = evalamb erhs env in 
			let env1 = (x, xval) :: env in 
				evalamb ebody env1
	| Op_e (e1, Plus,e2) -> ( evalamb e1 env) + ( evalamb e2 env)
	| Op_e (e1, Minus,e2) -> ( evalamb e1 env) - ( evalamb e2 env)
	| Op_e (e1, Times,e2) -> ( evalamb e1 env) * ( evalamb e2 env)
	| Op_e (e1, Div,e2) -> ( evalamb e1 env) / ( evalamb e2 env)
	| Op_e _ -> failwith ("Unknown Operand")
;;


type texp = 				(* Espressioni target *)
	| TVar of int 			(* indice a run time *) 	
	| TLet of int * texp * texp 	(* erhs e ebody *) 
	| TOp of texp * operand * texp
;;	

let rec getindex cenv x = match cenv with 	
	| [] -> failwith("Variable not found") 
	| y::yr -> if x=y then 0 else 1 + getindex yr x
;;

(* Compilation to target expressions with numerical indexes instead of
   symbolic variable names.  *)
let rec tcomp (e:texp)(cenv:' list) :texp = match e with 			(* Compilazione in codice intermedio *)
	| TVar x -> TVar (getindex cenv x) 
	| TLet (x, erhs, ebody) -> 
 		let cenv1 = x :: cenv in 
		TLet (x, tcomp erhs cenv, tcomp ebody cenv1) 
	| TOp(e1, op, e2) -> TOp(tcomp e1 cenv, op, tcomp e2 cenv)
;;

(* Evaluation of target expressions with variable indexes.  The
   run-time environment renv is a list of variable values (ints).  *)
let rec teval (e:texp)(renv:int list) :int = match e with 			(* Interpretazione in codice intermedio *)
	| TVar n -> List.nth renv n 
	| TLet (x, erhs, ebody) -> 
 		let xval = teval erhs renv in 
			let renv1 = xval :: renv in 
				teval ebody renv1 
	| TOp(e1, Plus, e2) -> teval e1 renv + teval e2 renv 
	| TOp(e1, Minus, e2) -> teval e1 renv - teval e2 renv 
	| TOp(e1, Times, e2) -> teval e1 renv * teval e2 renv 
	| TOp(e1, Div, e2) -> teval e1 renv / teval e2 renv
;;

let compile e = tcomp e [];;
let trun te = teval te [];;

(* Test: il fattoriale *)
(* Body del fattoriale: fun n -> if n < 1 then 1 else n * fact (n - 1) *)
let fact_body =	 
   Fun_e ( "n",
    If_e (Op_e (Var_e "n", LessThan, Int_e (1)), Int_e (1),
       Op_e (Var_e "n", Times, FunCall_e (Var_e "fact", Op_e (Var_e "n", Minus, Int_e (1))))))
;;

let fact_call = FunCall_e (Var_e "fact", (Int_e (4))) ;;		(* Chiamata: fact 4 *)
let fact4 = Letrec_e ("fact", fact_body, fact_call) ;;			(* Definizione ricorsiva del fattoriale chiamato sul valore 4 *)
eval fact4 ;;								(* Chiamata interprete *)
(* Risultato: - : exp = Int_e 24 *)

(* Test la somma *)
(* funzione ricorsiva: let rec sum n = if n<=0 then 0 else n+f(n-1) in f 3;; risultato=6 *)
let sum_body =	 
   Fun_e ( "n",
    If_e (Op_e (Var_e "n", LessThan, Int_e (0)), Int_e (0),
       Op_e (Var_e "n", Plus, FunCall_e (Var_e "sum", Op_e (Var_e "n", Minus, Int_e (1))))))
;;

let sum_call = FunCall_e (Var_e "sum", (Int_e (3))) ;;			(* Chiamata: sum 3 *)
let sum3 = Letrec_e ("sum", sum_body, sum_call) ;;			(* Definizione ricorsiva della funzione sum chiamato sul valore 3 *)
eval sum3 ;;								(* Chiamata interprete *)
(* Risultato: - : exp = Int_e 6 *)


let typecheck (x,y) :bool = match x with
	| "int" -> ( match y with
		| Int_e( u )-> true		(*oppure | Int_e u -> Bool_e true *)
		| _ -> false )
	| "bool" -> ( match y with
		| Int_e( u )-> true
		| _ -> false )
	| _ -> failwith("Not a valid type")
;;

let plus (x,y) = if (typecheck ("int", x) & typecheck ("int",y)) then ( match (x,y) with
			| (Int_e( v), Int_e( w)) -> Int_e (v+w) 	)
		     else failwith ("Type Error")
;;	
(* oppure 
let plus (x,y) = if (typecheck ("int", x) & typecheck ("int",y)) then Int_e ((Int_e x)+(Int_e y)) 
		     else failwith ("Type Error")
;;	
*)
plus(Int_e 3, Int_e 4);;

let minus (x,y) = if typecheck ("int", x) & typecheck ("int",y) then ( match (x,y) with
			| (Int_e v, Int_e w) -> Int_e (v-w) )
		     else failwith ("Type Error");;	
minus(Int_e 4, Int_e 3);;

let isZero (x,y) = if typecheck ("int", x) then ( match x with Int_e y -> Bool_e (y=0) )
		     else failwith ("Type Error");;	
isZero(Int_e 0, Int_e 6);;
isZero(Int_e 6, Int_e 0);;

let eq(x,y) = if typecheck ("int", x) & typecheck ("int",y) then ( match (x,y) with
			| (Int_e v, Int_e w) -> Bool_e (v=w) )
		     else failwith ("Type Error");;	
eq(Int_e 3, Int_e 4);;
eq(Int_e 3, Int_e 3);;



(* Ulteriore esempio -------------------------------------------------------------------------------*)

type exp =	CstI of int	| Prim of string * exp * exp;;

let e1 = CstI 17;;

let e2 = Prim("-", CstI 3, CstI 4);;

let e3 = Prim("+", Prim("*", CstI 7, CstI 9), CstI 10);;


let rec eval (e : exp) : int = match e with			(* Valutazione delle espressioni *)
	| CstI i -> i
    	| Prim("+", e1, e2) -> eval e1 + eval e2
    	| Prim("*", e1, e2) -> eval e1 * eval e2
    	| Prim("-", e1, e2) -> eval e1 - eval e2
    	| Prim _            -> failwith "unknown primitive";;

let e1v = eval e1;;
let e2v = eval e2;;
let e3v = eval e3;;


let rec evalm (e : exp) : int = match e with			(* Modifica del significato della sottrazione *)
    | CstI i -> i
    | Prim("+", e1, e2) -> evalm e1 + evalm e2
    | Prim("*", e1, e2) -> evalm e1 * evalm e2
    | Prim("-", e1, e2) -> let res = evalm e1 - evalm e2 in if res < 0 then 0 else res 
    | Prim _            -> failwith "unknown primitive";;

let e4v = evalm (Prim("-", CstI 10, CstI 27));;


