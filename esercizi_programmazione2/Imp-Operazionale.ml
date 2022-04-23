(* Imp-Operazionale.ml
Il file Imp-Operazionale.ml contiene la sintassi di un semplice linguaggio imperativo (con assegnamento, condizionale e while) e la sua semantica operazionale.	*)

(* Ambiente e operazioni *)

type 't env = string -> 't ;;

exception WrongBindlist ;;

let emptyenv(x) = function (y:string) -> x ;;
(* oppure let emptyenv (x)(y:string) =  x;; *)

let applyenv(x,(y:string)) = x y ;;

let bind((r: 'a env),(l:string),(e:'a)) = function lu -> if lu = l then e else applyenv(r,lu) ;;
(* oppure 
let bind ((r: 'a env),(l:string),(e:'a))(lu) = if lu = l then e else applyenv(r,lu) ;;  *)

let rec bindlist(r, il, el) = match (il,el) with
| ([],[]) -> r
	| i::il1, e::el1 -> bindlist (bind(r, i, e), il1, el1)
	| _ -> raise WrongBindlist ;;

(* Memoria e operazioni *)

type loc = int ;;

type 't store = loc -> 't ;;

let (newloc,initloc) =
let count = ref(-1) in
          		(fun () -> count := !count +1; !count), (fun () -> count := -1) ;;

let emptystore(x) = initloc(); function (y:loc) -> x ;;

let applystore((x: 'a store),(y: loc)) = x y ;;

let allocate((r: 'a store),(e:'a)) = let l = newloc() in
(l, function lu -> if lu = l then e else applystore(r,lu)) ;;

let update((r: 'a store),(l:loc),(e:'a)) = function lu -> if lu = l then e else applystore(r,lu) ;;   
(* oppure 
let update((r: 'a store),(l:loc),(e:'a))(lu:loc) = if lu=l then e else applystore(r,lu);; *)

(* Domini Sintattici *)

type ide = string ;;

type exp =  Eint of int		| Ebool of bool		| Den of ide		| Prod of exp * exp	| Sum of exp * exp 	| Diff of exp * exp 	| Eq of exp * exp 	| Not of exp
      	| Ifthenelse of exp * exp * exp			| Val of exp		| Newloc of exp
and com = 
       	| Assign of exp * exp
	| Cifthenelse of exp * com list * com list
	| While of exp * com list	   
;;

(* Domini Semantici *)

exception Nonstorable ;;
exception Nonexpressible ;;

type eval =	Int of int 	| Bool of bool	| Novalue		
and dval =  	Dint of int 	| Dbool of bool | Unbound	| Dloc of loc	
and mval = 	Mint of int	| Mbool of bool	 | Undefined
let evaltomval e = match e with
	| Int n -> Mint n	| Bool n -> Mbool n	| _ -> raise Nonstorable
let mvaltoeval m = match m with
	| Mint n -> Int n	| Mbool n -> Bool n	| _ -> Novalue
let evaltodval e = match e with
	| Int n -> Dint n	| Bool n -> Dbool n	| Novalue -> Unbound
let dvaltoeval e = match e with
	| Dint n -> Int n	| Dbool n -> Bool n	| Unbound -> Novalue
| Dloc n -> raise Nonexpressible
;;

(* Operations on Eval *)

let equ (x,y) = (match (x,y) with
| (Int(u), Int(w)) -> Bool(u = w)
   	| (Bool(u), Bool(w)) -> Bool(u = w)
        	| _ -> failwith ("type error")) ;;

let plus (x,y) = (match (x,y) with
   	| (Int(u), Int(w)) -> Int(u+w)
        	| _ -> failwith ("type error")) ;;
      
let diff (x,y) = (match (x,y) with
   	| (Int(u), Int(w)) -> Int(u-w)
        	| _ -> failwith ("type error")) ;;
      
let mult (x,y) = (match (x,y) with
   	| (Int(u), Int(w)) -> Int(u*w)
        	|_ -> failwith ("type error")) ;;     

let non x = (match x with
     	| Bool(y) -> Bool(not y) 
        	|_ -> failwith ("type error")) ;; 

(* semantica di espressioni *)
let rec sem ((e:exp),(r:dval env),(s: mval store)) = match e with
      	| Eint(n) -> Int(n)
      	| Ebool(b) -> Bool(b)
      	| Den(i) -> dvaltoeval(applyenv(r,i))
      	| Eq(a,b) -> equ(sem(a, r, s), sem(b, r, s))
      	| Prod(a,b) ->  mult (sem(a, r, s), sem(b, r, s))
      	| Sum(a,b) ->  plus (sem(a, r, s), sem(b, r, s))
      	| Diff(a,b)  ->  diff (sem(a, r, s), sem(b, r, s))
      	| Not(a) -> non(sem(a, r, s))
      	| Ifthenelse(a,b,c) -> let g = sem(a, r, s) in
               (if g = Bool(true) then sem(b, r, s) 
else (if g = Bool(false) then sem(c, r, s) else failwith ("nonboolean guard")))
| Val(e) -> let (v, s1) = semden(e, r, s) in (match v with 
	       	| Dloc n -> mvaltoeval(applystore(s1, n))
		| _ -> failwith("not a variable"))	
	| _ -> failwith ("nonlegal expression for sem") 

(* semantica di lista di espressioni *)
and semlist(el,(r: dval env),(s: mval store)) = match el with
| [] -> ([], s)
	| e::el1 -> let (v1, s1) = semden(e, r, s) in 
		let (v2, s2) = semlist(el1, r, s1) in
		       (v1 :: v2, s2)

(* semantica di espressioni come dval, per legarle nell'ambiente  *)
and semden((e: exp),(r: dval env),(s: mval store)) =  match e with
      	| Den(i) -> (applyenv(r,i), s)
      	| Newloc(e) -> let m = evaltomval(sem(e, r, s)) in 
let (l, s1) = allocate(s, m) in (Dloc l, s1)
     	| _ -> (evaltodval(sem(e, r, s)), s)

(* semantica di lista di espressioni come dval *)    
and semdv(dl,(r: dval env),(s: mval store)) = match dl with
	   | [] -> (r,s)
	   | (i,e)::dl1 -> let (v, s1) = semden(e, r, s) in semdv(dl1, bind(r, i, v), s1)

(* semantica di comandi *)
and semc((c: com),(r: dval env),(s: mval store)) = match c with
	   | Assign(e1, e2) -> let (v1, s1) = semden(e1, r, s) in (match v1 with
	     	| Dloc(n) -> update(s, n, evaltomval(sem(e2, r, s)))
	     	| _ -> failwith ("wrong location in assignment"))		 
	   | Cifthenelse(e, cl1, cl2) -> let g = sem(e, r, s) in
               	(if g = Bool(true) then semcl(cl1, r, s)
               	else (if g = Bool(false) then semcl (cl2, r, s) 
else failwith ("nonboolean guard")))
	   | While(e, cl) -> let g = sem(e, r, s) in
               	(if g = Bool(true) then semcl((cl @ [While(e, cl)]), r, s)
		else (if g = Bool(false) then s
			else failwith ("nonboolean guard")))

(* semantica di lista di comandi *)	     
and semcl((cl: com list),(r: dval env),(s: mval store)) = match cl with
	   | [] -> s
	   | c::cl1 -> semcl(cl1, r, semc(c, r, s))
;;	   

(* Es1: 
Estendere sintassi e semantica del linguaggio con un nuovo comando,  il "blocco" 'Block(decl, com list)'. 
Un blocco comprende una lista di "dichiarazioni" 'decl' e una lista di comandi 'com list'. 
Una "dichiarazione" e' una coppia di tipo 'ide * exp'. 
L'esecuzione di un blocco  'Block(decl, com list)' in un ambiente 'env' e con memoria 'st' consiste in
1) valutare la lista di dichiarazioni, ottenendo ambiente 'env1' e memoria 'st1'
2) valutare la lista di comandi nell'ambiente e memoria risultanti

Requisiti: estendere il tipo 'com' con il nuovo costrutto e la funzione 'semc' con una clausola per valutarne la semantica. 

Ci sono due esempi di definizione di blocco e di corrispondente esecuzione che dovrebbero poter funzionare in una implementazione corretta. 

Suggerimenti: introdurre tipi di dati e funzioni ausiliarie a piacere.
Sfruttare le funzioni 'semcl' e 'semdv' già definite nel file per le due parti del blocco.
*)

(* ESERCIZIO 1 *)

(*DA FARE: estendere exp in modo che comprendi Block … *)

(* funzione ausiliaria per eseguire un comando *)
let execCom (c:com) = semc(c,(emptyenv Unbound),(emptystore Undefined));;
(* val execCom : com -> mval store = <fun> *)

(* esempio 1 *)
(* semplice blocco: { DECL: int x = 1; BODY: int y = 0; y := x } *)
let (block1:com) =   (* dichiaro il comando *)
Block([("x", Newloc (Eint 1)); ("y", Newloc (Eint 0))],   (* decl *)
 		[Assign(Den "y",Val (Den "x"))] );;                 (* comandi *)

let (st: mval store) = execCom(block1);;    (* eseguo il comando *)

applystore(st, 0);;	(*  - : mval = Mint 1 *)
applystore(st, 1);;	(* - : mval = Mint 1 *)

(* esempio 2 *)
(*  blocchi annidati : 
{ DECL: int x = 1; BODY: x := x +1; { DECL: int y = x; BODY: x := y+1 }; x:= x + 1  } *)

let (block2:com) =
   Block( [("x", Newloc (Eint 1))],                          (* {int x = 1; *) 
      [Assign(Den "x",Sum(Val (Den "x"),Eint 1) );              (* x := x +1; *)
         Block ([("y", Newloc(Val(Den "x")))],                     (* {int y = x; *)
            [Assign(Den "x",Sum(Val (Den "y"), Eint 1))] );   (* x := y+1 }  *)	
        Assign(Den "x",Sum(Val (Den "x"), Eint 1))]);;            (* x:= x + 1  } *)

(* Con la soluzione fallisce qui con un eccezione *)
let (st2: mval store) = execCom(block2);;

applystore(st2, 0);;
applystore(st2, 1);;
(*  - : mval = Mint 4 *)
(* - : mval = Mint 2 *)


(* Es2:
Estendere sintassi e semantica del linguaggio precedente con procedure senza parametri e non ricorsive, e loro chiamata. 
In una dichiarazione, un identificatore può essere legato ad una procedura, che ha sintassi SimpleProc(block).  
La procedura può essere invocata con un nuovo comando CallSimple(exp).  
Se "P" è legata nell'ambiente a SimpleProc(block), l'invocazione di CallSimple(Den "P") eseguirà 'block' con scoping statico.

Ci sono due esempi di definizione di procedura e di corrispondente esecuzione che dovrebbero poter funzionare in una implementazione corretta.
*)

(* ESERCIZIO 2 *)
(* esempio 1*)
(*  invocazione di procedura semplice : 
{DECL Proc P = { DECL: int x = 1; BODY: x := x +1; 
{ DECL: int y = x; BODY: x := y+1 }; 
     x:= x + 1  }; 
BODY: Call P; Call P *)

let (com1:com) =
Block([("P", SimpleProc(([("x", Newloc (Eint 1))],                          (* {int x = 1; *) 
[Assign(Den "x",Sum(Val (Den "x"),Eint 1));              (* x := x +1; *)
Block ([("y", Newloc(Val(Den "x")))],                     (* {int y = x; *)
[Assign(Den "x",Sum(Val (Den "y"), Eint 3))]);              (* x := y+1 }  *)	
Assign(Den "x",Sum(Val (Den "x"), Eint 1))])))],           (* x:= x + 1  } *)
[CallSimple(Den "P");CallSimple(Den "P")])

let (st3: mval store) = execCom(com1);;

applystore(st3, 0);;
applystore(st3, 1);;
applystore(st3, 2);;
applystore(st3, 3);;

(* - : mval = Mint 6
 - : mval = Mint 2
 - : mval = Mint 6
 - : mval = Mint 2 *)

(* esempio 2*)
(*  invocazione di procedura semplice con rif a ambiente non locale: 
{DECL x = 1; Proc P = { DECL:  BODY: x := x +1; 
  	{ DECL: int y = x; BODY: x := y+1 }; 
     x:= x + 1  }; 
BODY: Call P; Call P *)

let (com2:com) =
Block([("x",Newloc (Eint 1)); ("P", SimpleProc(
([],                          (* {int x = 1; *) 
[Assign(Den "x",Sum(Val (Den "x"),Eint 1));              (* x := x +1; *)
Block ([("y", Newloc(Val(Den "x")))],                     (* {int y = x; *)
[Assign(Den "x",Sum(Val (Den "y"), Eint 3))]);              (* x := y+1 }  *)	
Assign(Den "x",Sum(Val (Den "x"), Eint 1))])))],           (* x:= x + 1  } *)
[CallSimple(Den "P");CallSimple(Den "P")])

let (st4: mval store) = execCom(com2);;

applystore(st4, 0);;
applystore(st4, 1);;
applystore(st4, 2);;
applystore(st4, 3);;

(* - : mval = Mint 11
 - : mval = Mint 2
 - : mval = Mint 7
 - : mval = Undefined *)


(* Es3:
Estendere il linguaggio dell'esercizio precedente con procedure con parametri e varie modalità di passaggio, cioè per nome, per riferimento e per valore.
*)

(* Si aggiunga il nuovo tipo: *)

type param =  (* parametro formale e suo tipo *) 
      | Const of ide
      | Ref of ide
      | Value of ide
;;

(* Si estenda il tipo 'exp' con la clausola:

      | Proc of param list * block

e il tipo 'com' con il comando

      | Call of exp * exp list

dove 'exp' e' l'astrazione procedurale e 'exp list' la lista di parametri attuali. La semantica di Call deve gestire correttamente il passaggio dei parametri modificando ambiente e memoria di conseguenza.
In particolare, se il parametro e' di tipo:
  Const("x"), allora "x" viene legata nell'ambiente al valore del parametro attuale
  Ref("x"), allora "x" viene legata nell'ambiente alla locazione associata al parametro attuale
  Value("x"), allora "x" viene legata nell'ambiente a una nuova variabile che viene inizializzata con il valore del parametro attuale. 
*)

(* SOLUZIONE *)

(* SYNTACTIC DOMAINS *)

type param =	Const of ide	| Ref of ide	| Value of ide ;;

type exp =	Eint of int	| Ebool of bool		| Den of ide		| Prod of exp * exp
| Sum of exp * exp	| Diff of exp * exp 	| Eq of exp * exp	| Not of exp
      	| Ifthenelse of exp * exp * exp			| Val of exp		| Newloc of exp
      	| SimpleProc of block	| Proc of param list * block

and decl = (ide * exp) list
and block = decl * com list
and com =	Assign of exp * exp		| Cifthenelse of exp * com list * com list
	   | While of exp * com list	   	| Block of block
	   | CallSimple of exp			| Call of exp * exp list
;;

(* SEMANTIC DOMAINS *)

type eval =	Int of int 	| Bool of bool	| Novalue
and proc =  exp * (dval env)   (* can be SimpleProc(_) or Proc(_,_) *)
and dval =	Dint of int 	| Dbool of bool | Unbound	| Dloc of loc	| Dprocval of proc 
and mval = 	Mint of int	| Mbool of bool | Undefined
let evaltomval e = match e with
	| Int n -> Mint n	| Bool n -> Mbool n	| _ -> raise Nonstorable
let mvaltoeval m = match m with
	| Mint n -> Int n	| Mbool n -> Bool n	| _ -> Novalue
let evaltodval e = match e with
	| Int n -> Dint n	| Bool n -> Dbool n	| Novalue -> Unbound
let dvaltoeval e = match e with
	| Dint n -> Int n	| Dbool n -> Bool n	| Unbound -> Novalue
| Dloc n -> raise Nonexpressible		| Dprocval p -> raise Nonexpressible
;;


let rec  sem((e: exp),(r: dval env),(s: mval store)) = match e with
	| Eint(n) -> Int(n)
	| Ebool(b) -> Bool(b)
	| Den(i) -> dvaltoeval(applyenv(r,i))
	
(* Non le riconosce valide *)
(*	| Eq(a,b) -> equ(sem(a, r, s), sem(b, r, s))	
	| Prod(a,b) ->  mult (sem(a, r, s), sem(b, r, s)) 
	| Sum(a,b) ->  plus (sem(a, r, s), sem(b, r, s))
	| Diff(a,b)  ->  diff (sem(a, r, s), sem(b, r, s))
	| Not(a) -> non(sem(a, r, s))	*)

	| Ifthenelse(a,b,c) -> let g = sem(a, r, s) in
            	(if g = Bool(true) then sem(b, r, s) 
    	else (if g = Bool(false) then sem(c, r, s) else failwith ("nonboolean guard")))
| Val(e) -> let (v, s1) = semden(e, r, s) in (match v with 
		| Dloc n -> mvaltoeval(applystore(s1, n))
		| _ -> failwith("not a variable"))
      	| _ -> failwith ("nonlegal expression for sem") 

and semlist(el,(r: dval env),(s: mval store)) = match el with
| [] -> ([], s)
	| e::el1 -> let (v1, s1) = semden(e, r, s) in 
		     let (v2, s2) = semlist(el1, r, s1) in (v1 :: v2, s2)

and semden ((e:exp),(r:dval env),(s: mval store)) =  match e with
      	| Den(i) -> (applyenv(r,i), s)
      	| Proc(params,b) -> (Dprocval(e,r), s)
      	| SimpleProc(b) -> (Dprocval(e,r), s)
      	| Newloc(e) -> let m = evaltomval(sem(e, r, s)) in 
let (l, s1) = allocate(s, m) in (Dloc l, s1)
| _ -> (evaltodval(sem(e, r, s)), s)
    
and semdv(dl,(r: dval env),(s: mval store)) = match dl with
	| [] -> (r,s)
	| (i,e)::dl1 -> let (v, s1) = semden(e, r, s) in semdv(dl1, bind(r, i, v), s1)

and semc((c: com),(r: dval env), (s: mval store)) = match c with
	| Assign(e1, e2) -> let (v1, s1) = semden(e1, r, s) in (match v1 with
		| Dloc(n) -> update(s, n, evaltomval(sem(e2, r, s)))
		| _ -> failwith ("wrong location in assignment")) 
	| Cifthenelse(e, cl1, cl2) -> let g = sem(e, r, s) in
           		(if g = Bool(true) then semcl(cl1, r, s)
               	else (if g = Bool(false) then semcl (cl2, r, s)
              		else failwith ("nonboolean guard")))
	| While(e, cl) -> let g = sem(e, r, s) in
               	(if g = Bool(true) then semcl((cl @ [While(e, cl)]), r, s)
		else (if g = Bool(false) then s else failwith ("nonboolean guard")))
	| CallSimple(e1) -> let (p, s1) = semden(e1,r,s) in (match p with 
               	| Dprocval(SimpleProc(b),x) ->  semb(b, x, s) (* SimpleProc(b),x) *) 
               	|  _ -> failwith ("CallSimple of something different from a SimpleProc"))
	| Call(e1, e2) -> let (p, s1) = semden(e1, r, s)  in (match p with 
               	|  Dprocval(Proc(params,b),x) -> (* calcolo la lista di par attuali come dval *)  
                 		let ((actparams: dval list), s2) = semlist(e2, r, s1) in  
                 		let ((env2: dval env), (s3:mval store)) = 
semparams(params, actparams, r, s2) in semb(b, env2, s3)
|  _ -> failwith ("Call of something different from a Proc"))    
| Block(b) -> semb(b, r, s)
	     
and semcl((cl: com list),(r: dval env),(s: mval store)) = match cl with
	| [] -> s
	| c::cl1 -> semcl(cl1, r, semc(c, r, s))
	   
and semb((dl, (cl: com list)),(r: dval env),(s: mval store)) = 
let (r1, s1) = semdv(dl, r, s) in semcl(cl, r1, s1)


and semparams((params: param list),(actparams : dval list),(r: dval env),(s: mval store)) =  
match (params, actparams) with
          		| ([],[]) -> (r,s)
          		| _  -> (r,s)
;;	  


(* ESEMPI *)

let execBl (b:block) = semb(b,(emptyenv Unbound),(emptystore Undefined));;
(* val execBl : block -> mval store = <fun> *)

let execCom (c:com) = semc(c,(emptyenv Unbound),(emptystore Undefined));;
(* val execCom : com -> mval store = <fun> *)

(* semplice blocco: { DECL: int x = 1; BODY: int y = 0; y := x } *)

let (block1:block) =
([("x", Newloc (Eint 1)); ("y", Newloc (Eint 0))],   (* decl *)
  [Assign(Den "y",Val (Den "x"))]);;                 (* comandi *)

let (st: mval store) = execBl(block1);;

applystore(st, 0);;	(*  - : mval = Mint 1 *)
applystore(st, 1);;	(* - : mval = Mint 1 *)

(*  blocchi annidati : 
{ DECL: int x = 1; BODY: x := x +1; 
  	{ DECL: int y = x; BODY: x := y+1 }; 
 x:= x + 1  } *)

let (block2:block) =
([("x", Newloc (Eint 1))],                          (* {int x = 1; *) 
[Assign(Den "x",Sum(Val (Den "x"),Eint 1));              (* x := x +1; *)
Block ([("y", Newloc(Val(Den "x")))],                     (* {int y = x; *)
[Assign(Den "x",Sum(Val (Den "y"), Eint 1))]);              (* x := y+1 }  *)	
Assign(Den "x",Sum(Val (Den "x"), Eint 1))]);;            (* x:= x + 1  } *)


(* Analgamente a come detto prima, fallisce per eccezione *)
let (st2: mval store) = execBl(block2);;

applystore(st2, 0);;
applystore(st2, 1);;
(*  - : mval = Mint 4 *)
(* - : mval = Mint 2 *)

(*  invocazione di procedura semplice : 
{DECL Proc P = { DECL: int x = 1; BODY: x := x +1; 
  	{ DECL: int y = x; BODY: x := y+1 }; 
     x:= x + 1  }; 
BODY: Call P; Call P *)

let (com1:com) =
Block([("P", SimpleProc(
([("x", Newloc (Eint 1))],                          (* {int x = 1; *) 
[Assign(Den "x",Sum(Val (Den "x"),Eint 1));              (* x := x +1; *)
Block ([("y", Newloc(Val(Den "x")))],                     (* {int y = x; *)
[Assign(Den "x",Sum(Val (Den "y"), Eint 3))]);              (* x := y+1 }  *)	
Assign(Den "x",Sum(Val (Den "x"), Eint 1))])))],           (* x:= x + 1  } *)
[CallSimple(Den "P");CallSimple(Den "P")])


(* Anche qui fallisce perchè genera eccezione *)
let (st3: mval store) = execCom(com1);;

applystore(st3, 0);;
applystore(st3, 1);;
applystore(st3, 2);;
applystore(st3, 3);;

(* - : mval = Mint 6
 - : mval = Mint 2
 - : mval = Mint 6
 - : mval = Mint 2 *)


(*  invocazione di procedura semplice con rif a ambiente non locale: 
{DECL x = 1; Proc P = { DECL:  BODY: x := x +1; 
  	{ DECL: int y = x; BODY: x := y+1 }; 
     x:= x + 1  }; 
BODY: Call P; Call P *)

let (com2:com) =
Block([("x",Newloc (Eint 1)); ("P", SimpleProc(
([],                          (* {int x = 1; *) 
[Assign(Den "x",Sum(Val (Den "x"),Eint 1));              (* x := x +1; *)
Block ([("y", Newloc(Val(Den "x")))],                     (* {int y = x; *)
[Assign(Den "x",Sum(Val (Den "y"), Eint 3))]);              (* x := y+1 }  *)	
Assign(Den "x",Sum(Val (Den "x"), Eint 1))])))],           (* x:= x + 1  } *)
[CallSimple(Den "P");CallSimple(Den "P")])


(* Fallisce generando eccezione per sem *)
let (st4: mval store) = execCom(com2);;

applystore(st4, 0);;
applystore(st4, 1);;
applystore(st4, 2);;
applystore(st4, 3);;

(* - : mval = Mint 11
 - : mval = Mint 2
 - : mval = Mint 7
 - : mval = Undefined *)






