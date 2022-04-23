(* Pila non modificabile: interfaccia *)
module type PILA = 
	sig
		type 'a stack
		val create		: int			-> 'a stack
		val emptyStack	: int * 'a option		-> 'a stack	
		val push		: 'a option * 'a stack 	-> 'a stack
val pop			: 'a stack 		-> 'a stack
val top			: 'a stack 		-> 'a option
val empty		: 'a stack 		-> bool
val lungh		: 'a stack 		-> int
exception EmptyStack
exception FullStack 
	end
;;


(* Pila non modificabile: semantica semplice e algebrica
module SemPila : PILA = 
struct
		type 'a stack = 
			| Empty of int
			| Push of 'a stack * 'a
		exception EmptyStack
		exception FullStack
		let create n = Empty(n)
		let emptyStack(n,x) = Empty(n)
		let rec max = function
			| Empty n -> n		
			| Push(p,a) -> max(p)
		let rec lungh = function
			| Empty n -> 0			(* opp Empty _ -> 0 *)
			| Push(p,a) -> 1+lungh(p)	(* opp Push(p, _ ) -> 1+lungh(p)
		lungh(Empty n) = 0
		lungh(Push(p,a)) = 1 + lungh(p)
		let Push(p,a) = if lungh(p) = max(p) than raise FullStack else Push(p,a)
	push(a, p) = Push(p,a)
		let pop = function
			| Push(p,a) -> p
			| Empty n -> raise EmptyStack
		pop(Push(p,a)) = p
		let top = function
			| Push(p,a) -> a
			| Empty n -> raise EmptyStack
		top(Push(p,a)) = a
		let empty = function
			| Push(p,a) -> false
			| Empty n -> true
		empty(Empty n) = true
		empty(Push(p,a)) = false
end
;;


*)

(* Pila non modificabile : implementazione *)
module ImpPila : PILA = 
	struct
		type 'a stack = Pila of ('a option array) * int
		exception EmptyStack
		exception FullStack
		let create n = Pila(Array.make n None, -1)
		let emptyStack(nm, x) = Pila( Array.create nm x, -1 ) 
		let push(x, Pila(s,n)) = if n=(Array.length(s) -1) then raise FullStack
					else (Array.set s (n+1) x; Pila(s, n+1))
		let top(Pila(s,n)) = if n=(-1) then raise EmptyStack else Array.get s n
		let pop(Pila(s,n)) = if n=(-1) then raise EmptyStack else  Pila(s, n-1)
		let empty(Pila(s,n)) = if n=(-1) then true else false
		let lungh(Pila(s,n)) = n
	end
;;

(* Se invece non per ogni 'a non specifico la clausola option, posso usare la seconda implementazione che cambia dalla precedente solo nell’utilizzo dei nomi some 
(* Pila non modificabile: interfaccia *)
module type PILA = 
	sig
		type 'a stack
		val create		: int			-> 'a stack
		val emptyStack	: int * 'a option		-> 'a stack	
		val push		: 'a * 'a stack 		-> 'a stack
val pop			: 'a stack 		-> 'a stack
val top			: 'a stack 		-> 'a
val empty		: 'a stack 		-> bool
val lungh		: 'a stack 		-> int
exception EmptyStack
exception FullStack 
	end
;;

module ImpPila: PILA = 
struct 
type 'a stack = IPila of ('a option array) * int 
exception EmptyStack 
exception FullStack 
let create n = IPila(Array.make n None, -1) 
		let emptyStack(nm, x) = IPila( Array.create nm x, -1 ) 
let push(x, IPila(s,n)) = if n = (Array.length s - 1) then raise FullStack 
else (Array.set s (n + 1) (Some x) ; IPila(s, n + 1)) 
let top(IPila(s,n)) = if n = -1 then raise EmptyStack 
      else (match Array.get s n with | Some y -> y)
let pop(IPila(s,n)) = if n = -1 then raise EmptyStack else IPila(s, n -1) 
let empty(IPila(s,n)) = if n = -1 then true else false 
let lungh(IPila(s,n)) = n 
end 
;;

*)

(* Pila modificabile : interfaccia *)
module type MPILA =
	sig
		type 'a stack
		val create		: int			-> 'a stack
		val emptyStack	: int * 'a option		-> 'a stack	
		val push		: 'a option * 'a stack 	-> unit
val pop			: 'a stack 		-> unit
val top			: 'a stack 		-> 'a option
val empty		: 'a stack 		-> bool
val lungh		: 'a stack 		-> int
val svuota		: 'a stack 		-> unit
val access		: 'a stack * int		-> 'a option
exception EmptyStack
exception FullStack 
		exception WrongAccess
	end
;;

(* Pila modificabile : semantica
module SemMPila : MPILA = 
struct
		type 'a stack = ('a SemPila.stack) ref
		exception EmptyStack
		exception FullStack
		exception WrongAccess
		let create n = Empty(n)
		let emptyStack(n,x) = ref(SemPila.emptyStack(n,x))
		let lungh x = SemPila.lungh(!x)
		let push(p,a) = x:= SemPila.push(a,!p)
		let pop x = x:= SemPila.pop(!x)
		let top x = SemPila.top(!x)
		let empty x = SemPila.empty(!x)
		let rec svuota x = if empty(x) then () else (pop x; svuota x )
		let rec faccess(x,n) = if n=0 then SemPila.top(x) 
else faccess(SemPila.pop(x); n-1)
		let access(x,n) = let nofpops = lungh(x) -1 -n in 
					if nofpops<0 then raise WrongAccess
					else faccess( !x, nofpops)
end
;;
*)

(* Pila modificabile : implementazione *)
module ImpMPila : MPILA = 
	struct
		type 'a stack = ('a option array) * int ref
		exception EmptyStack
		exception FullStack
		exception WrongAccess
		let create n = ((Array.make n None, ref(-1)) : 'a stack)
		let emptyStack(nm, (x : 'a option)) = (( Array.create nm x, ref(-1) ) : 'a stack )
		let push(x, ((s,n) : 'a stack)) = if !n = (Array.length(s) -1) then raise FullStack
					else (Array.set s (!n+1) x; n := !n+1)
		let top((s,n) : 'a stack) = if !n = (-1) then raise EmptyStack else Array.get s !n
		let pop((s,n) : 'a stack) = if !n = (-1) then raise EmptyStack else n := !n-1
		let empty((s,n) : 'a stack) = if !n= (-1) then true else false
		let lungh((s,n) : 'a stack) = !n
		let svuota((s,n) : 'a stack ) = n := (-1)
let access(((s,n) : 'a stack),k) = Array.get s k	
	end
;;

(* Quando le liste sono definite bene, implementare anche questa seconda parte
module ImpMPila: MPila = 
struct 
type 'a stack = ('a list) ref * int ref * int 
exception EmptyStack 
exception FullStack 
exception WrongAccess
let create n = (ref [], ref 0, n)
 
let push(x,(s,l,n)) = if !l = n then raise FullStack else (s := x::!s; l := !l + 1) 
let top(s,l,n) = match !s with 
| [] -> raise EmptyStack 
| x :: xs -> x 
let pop(s,l,n) = match !s with 
| [] -> raise Empty 
| x :: xs -> (s := xs; l := !l - 1) 
let is_empty(s,l,n) = if !l = 0 then true else false 
let lungh(s,l,n) = !l 
end
;;
*)

(* NON FUNZIONA
 Lista non polimorfa: interfaccia 

module type INTLIST = 
	sig
		type int list
		val create		: int		-> 'a stack 
		val emptyList		: int list		-> int list	
		val cons		: int * int list 	-> int list
val tail			: int list 	-> int list
val head		: int list		-> int
val empty		: int list		-> bool
val lungh		: int list 	-> int
exception EmptyList
	end
;;

(* Lista: implementazione a heap *)
module ImplListaInt : INTLIST = 
	struct
		type intlist = int
		let heapSize = 100
		let heads = Array.create heapSize 0
		let tails = Array.create heapSize 0
		let next = ref(0)
		let emptyHeap = let index = ref(0) in
			while !index < heapSize do
				Array.set tails !index (!index +1);
				index := !index +1
			done;
			Array.set tails(heapSize -1) (-1);
			next := 0
		exception FullHeap
		excetpionEmptyList
		let emptyList = -1
		let empty l = if l= -1 then true else false
		let cons(n,l) = if !next = -1 then raise FullHeap
				else (let newPoint = !next in 
next := Array.get tails !next;
Array.set heads newPoint n;
Array.set tails newPoint l;
newPoint )	
		let tails l = if empty l then raise EmptyList else Array.get tails l
		let head l = if empty l then raise EmptyList else Array.get heads l
		let rec lungh l = if l= -1 then 0 else 1 + lungh( tail l)
	end
;;

*)

(* Ambiente : interfaccia *)
module type ENV =
	sig
		type 'a env
		val emptyEnv 	: 'a 				-> 'a env
		val bind 	: 'a env * string * 'a 		-> 'a env
		val bindList	: 'a env * (string list) * ('a list) 	-> 'a env
		val applyEnv 	: 'a env * string 		-> 'a
		exception WrongBindList
	end
;;

(* Ambiente : semantica *)
module FunEnv : ENV =
	struct
		type 'a env = string -> 'a
		exception WrongBindList
		let emptyEnv(x) = function (y:string) -> x (* x è un valore di default*)
		let applyEnv(x,y) = x y
		let bind(r,l,e) = function lv -> if lv=l then e else applyEnv(r,lv)
		let rec bindList(r,il,el) = match (il,el) with
			| ([],[]) -> r
			| (i::ill, e::ell) -> bindList(bind(r,i,e),ill,ell)
			| _ -> raise WrongBindList
	end
;;

(* Ambiente : implementazione *)
module ListEnv : ENV = 
	struct
		type 'a env = (string * 'a) list
		exception WrongBindList
		let emptyEnv(x) = [ ( " ", x ) ]
		let rec applyEnv(x,y) = match x with
			| [(_ , e)] -> e
			| (il, el)::x1 -> if y=il then el else applyEnv(x1,y)
			| [] -> failwith("Wrong Env")
		let bind(r,l,e) = (l,e)::r (* aggiunge una coppia in cima *)
		let rec bindList(r, il,el) = match (il,el) with
			| ([],[]) -> r
			| (i::ill,e::ell) -> bindList(bind(r,i,e), ill,ell)
			| _ -> raise WrongBindList
	end
;;

(* La memoria: specifica *)
module type STORE =
	sig
		type 'a store
		type loc
		val emptyStore	: 'a 			-> 'a store
		val allocate 		: 'a store * 'a 		-> loc * 'a store
		val update 		: 'a store * loc * 'a 	-> 'a store
		val applyStore 	: 'a store * loc 		-> 'a
	end
;;

(* La memoria: implementazione *)
module FunStore : STORE =
	struct
		type loc = int
		type 'a store = loc -> 'a
		let(newLoc, initLoc) = 
			let count = ref(-1) in
			((fun()->count := !count +1; !count), (fun()->count := -1))
		let emptyStore(x) = initLoc();
			function y -> x
		let applyStore(x,y) = x y
		let allocate((r:'a store),(e:'a))=let l=newLoc() in
			(l,fun lv -> if lv=1 then e else applyStore(r,lv))
		let update((r : 'a store),(l : loc),(e : 'a)) = 
fun lv -> if lv=1 then e else applyStore(r,lv)
	end
;;

(* NON FUNZIONA 
(* DOMINI DEI VALORI *)
exception NonStorable ;;
exception NonExpressible ;;

type eval =
	| Int of int
	| Bool of bool
	| NoValue
;;

type dval = 
	| DInt of int
	| DBool of bool
	| UnBound
;;

type mval = 
	| MInt of int
	| MBool of bool
	| Undefined
;;

(* Casting tra i vari tipi di valori *)
let evalTOmval e = match e with
	| Int e = MInt e
	| Bool e = MBool e
	| _ -> raise NonStorable 
;;

…

*)


