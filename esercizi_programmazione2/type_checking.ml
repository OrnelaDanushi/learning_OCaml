(* Programmare un controllore di tipo *)

type ide = string ;;
type loc = int ;;
type param = Val of ide | Name of ide | Ref of ide ;;

type exp =	
	| Eint of int 	
	| Ebool of bool 	
	| Den of ide 	
	| Prod of exp * exp 
	| Sum of exp * exp 	
	| Diff of exp * exp 	
	| Eq of exp * exp 
	| Minus of exp 		
	| IsZero of exp 	
	| Or of exp*exp
	| And of exp*exp 
	| Not of exp 		
	| Ifthenelse of exp * exp * exp 	
	| Let of ide * exp * exp 
 	| Fun of param * exp 			(* | Fun of ide * exp 	*)
	| FunCall of exp * exp 	

 	(*
 	| Letrec of ide * exp * exp
	| RecFun of ide * ide * exp
 	*)
;;

type 't env = ide -> 't ;;				(*ambiente polimorfo*)
let emptyenv (v: 't) = function x -> v ;;
(* oppure let emptyenv (v:'t) (x) = v ;; *)
let env0 = (emptyenv Unbound) ;;			(*ambiente default*)
let applyenv (r: 't env) (i: ide) = r i ;;

let bindE (r: 't env) (i: ide) (v: 't) = function x -> if x = i then v else applyenv r x ;;
(* oppure
let bind (r: 't env) (i: ide) (v: 't) (x: ide ) = if x = i then v else applyenv r x ;;	*)

type 't store = loc -> 't ;;				(*ambiente polimorfo*)
let store0 = (emptyenv Undef);;
let applystore (s: 't store) (l: loc) = s l ;;
let bindM (s: 't store) (l: loc) (v: 't) = function x -> if x = l then v else applystore s x ;;


(* tipi memorizzabili ed esprimibili *)
type mvT = Int of int | Bool of bool | Undef ;;
type evT =					
	| Loc of loc
	| Unbound  
	| FunVal of evFun 	
	| ExpVal of evExp
 	and evFun = param * exp * evT env
  	and evExp = exp * evT env ;;

  	(*
	| RecFunVal of ide * evFun 
		and evFun = ide * exp * evT env		(* se evFun le diamo scoping statico: si porta appresso l’ambiente *)

	(* NON FUNZIONA 
	and makefunrec (f, arg, body, r) = let functional (rr: evT env) = 
			bind (r, f, FunVal(arg,body,rr)) in
				let rec(rfix:evT env) = function x -> (functional rfix) x in
						FunVal(arg,body,rfix) 
	L’ambiente calcolato da functional contiene l’associazione tra il nome della funzione e la chiusura con l’ambiente soluzione della definizione 
	*)

	(*  La definizione di evFun mostra che una astrazione funzionale è una chiusura, che comprende: 
	nome del parametro formale : ide
	codice della funzione dichiarata : exp
	ambiente al momento della dichiarazione : evT env 
		
	| RecFunVal of ide * evFun 
		and evFun = ide * exp		 	se evFun le diamo scoping dinamico: le togliamo l’ambiente appresso *)
	;;
	*)

(* runtime support *)

let typecheck (s: string) (v: mvT) : bool = match s with	(* type checking *)
	| "int" -> (match v with
		| Int(_) -> true 
		|_ -> false) 
	| "bool" -> (match v with
		| Bool(_) -> true 
		| _ -> false) 
	|_ -> failwith("not a valid type") ;;


(* funzioni primitive *)

let prod x y = if (typecheck "int" x) && (typecheck "int" y) then (match (x,y) with 
			(Int(n),Int(u)) -> Int(n*u))
		else failwith("Type error") ;;

let sum x y = if (typecheck "int" x) && (typecheck "int" y) then (match (x,y) with
			(Int(n),Int(u)) -> Int(n+u))
		else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y) then (match (x,y) with
			(Int(n),Int(u)) -> Int(n-u))
		else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y) then (match (x,y) with
			(Int(n),Int(u)) -> Bool(n=u))
		else failwith("Type error");;

let minus x = if (typecheck "int" x)  then (match x with
	   		Int(n) -> Int(-n))
		else failwith("Type error");;

let iszero x = if (typecheck "int" x) then (match x with
			Int(n) -> Bool(n=0))
		else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y) then (match (x,y) with
			 (Bool(b),Bool(e)) -> (Bool(b||e)))
		else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y) then (match (x,y) with
			(Bool(b),Bool(e)) -> Bool(b&&e))
		else failwith("Type error");;

let non x = if (typecheck "bool" x) then (match x with
			| Bool(true) -> Bool(false) 
			| Bool(false) -> Bool(true))
		else failwith("Type error");;

(*contatore di locazioni: e' un puntatore!!*)
(* la presenza di s e' concettuale: la newloc dovrebbe dipendere dallo store... *)
let count = ref 0;;
let newloc (s : mvT store) = (incr count; !count);;

let rec dval (e: exp) (r: evT env) (s: mvT store) : evT = match e with
	| Fun(p, a) -> FunVal(p, a, r)
	| Den id -> (applyenv r id)
	| _ -> Loc (newloc s) ;;

(*
let rec eval (e : exp) (r : evT env) : evT = match e with		(* interprete *)
	| Eint n -> Int n 
	| Ebool b -> Bool b 
	| IsZero a -> iszero (eval a r) 
	| Den i -> applyenv r i 
	| Eq(a, b) -> eq (eval a r) (eval b r) 
	| Prod(a, b) -> prod (eval a r) (eval b r)
	| Sum(a, b) -> sum (eval a r) (eval b r) 
	| Diff(a, b) -> diff (eval a r) (eval b r) 
	| Minus a -> minus (eval a r) 
	| And(a, b) -> et (eval a r) (eval b r) 
	| Or(a, b) -> vel (eval a r) (eval b r) 
	| Not a -> non (eval a r) 
	| Ifthenelse(a, b, c) -> let g = (eval a r) in
			if (typecheck "bool" g) then (if g = Bool(true) then (eval b r) else (eval c r))
			else failwith ("nonboolean guard") 
	| Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) 
		(* L’espressione e2 (ovvero il corpo del blocco) è valutata nell’ambiente “esterno”	
  		esteso con l’associazione tra nome i e valore di e1 *) 
	
	| Fun(i, a) -> FunVal(i, a, r) 								(* Scoping statico *)
	| FunCall(f, eArg) -> let fClosure = (eval f r) in (match fClosure with		
			| FunVal(arg, fBody, fDecEnv) -> eval fBody (bind fDecEnv arg (eval eArg r)) 
	| RecFunVal(f, (arg, fBody, fDecEnv)) -> let aVal = (eval eArg r) in
			let rEnv = (bind fDecEnv f fClosure) in
				let aEnv = (bind rEnv arg aVal) in eval fBody aEnv 
	| _ -> failwith("non functional value")) 
	
 	(* 	
 	| FunCall(f, a) -> (match (eval f r) with 
		| FunVal(i, b, r1) -> eval b bind(r1, i, (eval a r)) 
	| _ -> failwith("non functional value"))
	Il corpo della funzione viene valutato nell’ambiente ottenuto legando 
 	i parametri formali ai valori dei parametri attuali nell’ambiente r1, 
  	nel quale era stata valutata l’astrazione   
	*)

	(*
	| Fun(i, a) -> FunVal(i, a) 								Scoping dinamico 
	| FunCall(f, a) -> (match (eval f r) with 
		| FunVal(i, b) -> eval b bind(r, i, (eval a r)) 
	| _ -> failwith("non functional value"))
	Il corpo della funzione viene valutato nell’ambiente ottenuto legando 
 	i parametri formali ai valori dei parametri attuali nell’ambiente r, 
  	quello nel quale viene effettuata la chiamata 
	*)

	| Letrec(f, funDef, letBody) -> (match funDef with
          | Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in eval letBody r1 
          | _ -> failwith("non functional def"))
;;


(* esempti di valutazione *)
eval (Eint (2))(emptyenv Unbound);;
eval (Ebool (true))(emptyenv Unbound);;
eval (Ebool (false))(emptyenv Unbound);;
eval (IsZero (Eint 2))(emptyenv Unbound);;
eval (Den ("ciao"))(emptyenv Unbound);;
eval (Eq ((Eint 2),(Eint 2)))(emptyenv Unbound);;
eval (Eq ((Eint 2),(Eint 3)))(emptyenv Unbound);;
eval (Prod ((Eint 2),(Eint 3)))(emptyenv Unbound);;
eval (Sum ((Eint 2),(Eint 3)))(emptyenv Unbound);;
eval (Diff ((Eint 5),(Eint 3)))(emptyenv Unbound);;
eval (Minus (Eint (-3)))(emptyenv Unbound);;
eval (Minus (Eint (3)))(emptyenv Unbound);;
eval (And ((Ebool true),(Ebool true)))(emptyenv Unbound);;
eval (And ((Ebool true),(Ebool false)))(emptyenv Unbound);;
eval (Or ((Ebool true),(Ebool false)))(emptyenv Unbound);;
eval (Or ((Ebool false),(Ebool false)))(emptyenv Unbound);;
eval (Not (Ebool false))(emptyenv Unbound);;
eval (Not (Ebool true))(emptyenv Unbound);;
eval (Ifthenelse ((Ebool true),(Eint 1),(Eint 0)))(emptyenv Unbound);;
eval (Ifthenelse ((Ebool false),(Eint 1),(Eint 0)))(emptyenv Unbound);;

eval (Let("x", 									(* Valutazione -: evT = Int 3*)
	Sum(Eint 1, Eint 0), 
	Let("y", 
		Ifthenelse(Eq(Den "x", Eint 0), Diff(Den "x", Eint 1), 
  		Sum(Den "x", Eint 1)), 
	Let("z", Sum(Den "x", Den "y"), Den "z"))
	)) (emptyenv Unbound)
 ;;
let x = 1+0 in let y = if x = 0 then x-1 else x+1 in let z = x+y in z;;  	(* Sintassi -: int = 3*)

eval (Letrec("fact",								(* Valutazione -: evT = Int 6*)
	Fun("n",
	Ifthenelse(Eq(Den "n", Eint 0), Eint 1, Prod(Den "n", FunCall(Den "fact", Diff(Den "n", Eint 1))))),
	FunCall(Den "fact", Eint 3))) (emptyenv Unbound) ;;

let rec fact = fun n -> if n = 0 then 1 else n * fact (n-1) in fact(3);;	(* Sintassi -: int = 6*)

*)




(* Ulteriore versione *)
type 't env = (string * 't) list

let rec lookup x y = match x with
	| (i1,e1) :: x1 -> if y = i1 then e1 else lookup x1 y
	| [] -> failwith("wrong env") ;;

type typ = TypI (* int *) | TypB (* bool *) | TypF of typ * typ (* (argumenttype, resulttype)  *)

type tyexpr =								(* abstract syntax with explicit types *)
	| CstI of int	
	| CstB of bool	
	| Var of string
	| Let of string * tyexpr * tyexpr	
	| Prim of string * tyexpr * tyexpr
	| If of tyexpr * tyexpr * tyexpr		
	| Letfun of string * string * typ * tyexpr * typ * tyexpr (* (f, x, xTyp, fBody, rTyp, letBody *)
	| Call of tyexpr * tyexpr
;;

let rec typ (e: tyexpr)(env: typ env) : typ = match e with		(* Type checking *)
	| CstI i -> TypI
	| CstB b -> TypB
	| Var x  -> lookup env x
	| Prim(ope, e1, e2) -> let t1 = typ e1 env in 

let t2 = typ e2 env in (match (ope, t1, t2) with
	| ("*", TypI, TypI) -> TypI
	| ("+", TypI, TypI) -> TypI
      	| ("-", TypI, TypI) -> TypI
      	| ("=", TypI, TypI) -> TypB
      	| ("<", TypI, TypI) -> TypB
      	| ("&", TypB, TypB) -> TypB
      	| _   -> failwith "unknown op, or type error")
	| Let(x, eRhs, letBody) -> let xTyp = typ eRhs env in
      		let letBodyEnv = (x, xTyp) :: env in typ letBody letBodyEnv
    	| If(e1, e2, e3) -> (match typ e1 env with
      		| TypB -> let t2 = typ e2 env in let t3 = typ e3 env in
                		if t2 = t3 then t2
                		else failwith "If: branch types differ"
      		| _    -> failwith "If: condition not boolean")
    	| Letfun(f, x, xTyp, fBody, rTyp, letBody) -> let fTyp = TypF(xTyp, rTyp) in
      		let fBodyEnv = (x, xTyp) :: (f, fTyp) :: env in
      		let letBodyEnv = (f, fTyp) :: env in
      			if typ fBody fBodyEnv = rTyp then typ letBody letBodyEnv
      			else failwith ("Letfun: return type in " ^ f)
    	| Call(Var f, eArg) -> (match lookup env f with
      		| TypF(xTyp, rTyp) -> if typ eArg env = xTyp then rTyp
		else failwith "Call: wrong argument type"
		| _ -> failwith "Call: unknown function")
	| Call(_, eArg) -> failwith "Call: illegal function in call"
;;

let typeCheck e = typ e [];;


(* versione completa *)

let rec eval (e : exp) (r : evT env) (s : mvT store) : mvT = match e with
	| Eint n -> Int n
	| Ebool b -> Bool b
	| Den id -> let tmp = (dval e r s) in (match tmp with
		| Loc lo -> applystore s lo
		| ExpVal(e1, r1) -> eval e1 r1 s
		| _ -> failwith("DenExp error"))
	| IsZero a -> iszero (eval a r s)
	| Eq(a, b) -> eq (eval a r s) (eval b r s)
	| Prod(a, b) -> prod (eval a r s) (eval b r s)
	| Sum(a, b) -> sum (eval a r s) (eval b r s)
	| Diff(a, b) -> diff (eval a r s) (eval b r s)
	| Minus a -> minus (eval a r s)
	| And(a, b) -> et (eval a r s) (eval b r s)
	| Or(a, b) -> vel (eval a r s) (eval b r s)
	| Not a -> non (eval a r s)
	| Ifthenelse(a, b, c) -> let g = (eval a r s) in
		if (typecheck "bool" g)
			then (if g = Bool(true) then (eval b r s) else (eval c r s))
		else failwith ("Guard error")
	| Let(id, e1, e2) -> let tmp = (dval e1 r s) in (match tmp with
		| FunVal(p, a, r) -> eval e2 (bindE r id tmp) s
		| ExpVal(e3, r1) -> let tmp = (dval e3 r1 s) in (match tmp with
			| Loc lo -> eval e2 (bindE r id tmp) (bindM s lo (eval e3 r1 s))
			| _ -> failwith("ExpVal error"))
		| Loc lo -> let r1 = (bindE r id tmp) in
			let s1 = (bindM s lo (eval e1 r s)) in eval e2 r1 s1
		|_ -> failwith("LetExp error"))
		| FunCall(id, arg) -> let fClosure = (dval id r s) in (match fClosure with
			| FunVal(par, fBody, fDecEnv) -> auxval fClosure arg r s
			| _ -> failwith("FunCallExp error"))
	and auxval (e : evT) (arg : exp) (r : evT env) (s : mvT store) : mvT = match e with
		| FunVal(par, fBody, fDecEnv) -> (match par with
			| Val id -> let tmp = (newloc s) in
				eval fBody (bindE fDecEnv id (Loc tmp)) (bindM s tmp (eval arg r s))
			| Name id -> let tmp = (ExpVal(arg, r)) in
				eval fBody (bindE fDecEnv id tmp) s
			| (* si passa l'ambiente al momento della chiamata di funzione *)
			Ref id -> let tmp = (dval arg r s) in (match tmp with
				| Loc lo -> eval fBody (bindE fDecEnv id tmp) s
				| (* se e' una locazione nuova, lo e' indefinito in s *)
					_ -> failwith("RefPar error") ) )
				|_ -> failwith("FunCalltExp error");;


(* ============================= TESTS ================= *)
let env0 = emptyenv Unbound;;								(* basico: no let *)

let e1 = FunCall(Fun(Ref "y", Sum(Den "y", Eint 1)), Eint 3);;
eval e1 env0;;

let e2 = FunCall(Let("x", Eint 2, Fun(Ref "y", Sum(Den "y", Den "x"))), Eint 3);;
eval e2 env0;;

(*Non torna *)
let e2 = Let("x",Eint 2, "f", Fun(Ref "y", FunCall(Fun(Ref "x", Let("x", Eint 2, Fun(Ref "y",
	Sum(Den "y", Den "x"))), Eint 3))));;
eval e2 env0;;
