exp

(* Definizione *)
type exp =
	| EAdd of exp * exp
	| ESub of exp * exp
	| EMul of exp * exp
	| EDiv of exp * exp
	| EInt of int 
(* valutato come: 
	type exp =
    		| EAdd of exp * exp
  		| ESub of exp * exp
  		| EMul of exp * exp
  		| EDiv of exp * exp
  		| EInt of int

ovvero lo stesso testo ma senza ;; di fine comando	*)
;;

foo

(* Definizione *)
type foo =
| Nothing
| Int of int
| Pair of int * int
| String of string ;;
(* valori del tipo foo:
 	Nothing ;;
	Int 3 ;;
	Pair ( 4, 5) ;;
	String “hello” ;;
*)

(* Uso 1:
	applico un conteggio al tipo foo
	get_count : foo -> int = <fun>
*)
let get_count f = match f with 
   | Nothing -> 0
   | Int ( n ) -> n
   | Pair ( n, m ) -> n+m
   | String ( s ) -> 0 ;;
(* Uso della funzione
	get_count Nothing;;
	get_count (Int 2);;
	get_count (Pair (2,3));;
	get_count (String “hello”);;
	
	Sono molto importanti le tonde che racchiudono il tipo di dato insieme 
*)

giorno

(* Definizione *) 
type giorno = Lun | Mar | Mer | Gio | Ven | Sab | Dom ;;

(* Uso 1: 
trasformo il tipo di dato in stringhe
string_of_giorno: giorno -> string = <fun>
*)
let string_of_giorno g = match g with
   | Lun -> "Lunedì"
   | Mar -> "Martedì"
   | Mer -> "Mercoledì"
   | Gio -> "Giovedì"
   | Ven -> "Venerdì"
   | Sab -> "Sabato"
   | Dom -> "Domenica" ;;

(* Uso 2:
trasformo il tipo di dato in interi
int_of_giorno: giorno -> int = <fun>
*)
let int_of_giorno g = match g with
   | Lun -> 1
   | Mar -> 2
   | Mer -> 3
   | Gio -> 4
   | Ven -> 5
   | Sab -> 6
   | Dom -> 7 ;;




