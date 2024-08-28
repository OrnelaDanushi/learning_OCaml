
type exp =				(* Definizione delle espressioni *)
	| EAdd of exp * exp
	| ESub of exp * exp
	| EMul of exp * exp
	| EDiv of exp * exp
	| EInt of int ;;
 
(* valutato con lo stesso testo ma senza ;; di fine comando	*)

type foo =				(* Definizione di foo con esempi d'uso *)
	| Nothing			(* Nothing ;; *)
	| Int of int			(* Int 3 ;; *)
	| Pair of int * int		(* Pair (4, 5) ;; *)
	| String of string ;;		(* String "hello" ;; *)

(* applico un conteggio al tipo foo			  get_count : foo -> int = <fun> *)
let get_count f = match f with 
   | Nothing -> 0			(* get_count Nothing ;; *)
   | Int ( n ) -> n			(* get_count (Int 2) ;; *)
   | Pair ( n, m ) -> n+m		(* get_count (Pair (2,3)) ;; *)
   | String ( s ) -> 0 ;;		(* get_count (String "hello") ;; *)
   
(* Sono importanti le () che racchiudono il tipo di dato insieme dato come input *)

(* Definizione *) 
type giorno = Lun | Mar | Mer | Gio | Ven | Sab | Dom ;;

(* trasformo il tipo di dato giorno in stringhe 	string_of_giorno: giorno -> string = <fun> *)
let string_of_giorno g = match g with
   | Lun -> "Lunedì"
   | Mar -> "Martedì"
   | Mer -> "Mercoledì"
   | Gio -> "Giovedì"
   | Ven -> "Venerdì"
   | Sab -> "Sabato"
   | Dom -> "Domenica" ;;

(* trasformo il tipo di dato giorno in interi	        int_of_giorno: giorno -> int = <fun> *)
let int_of_giorno g = match g with
   | Lun -> 1
   | Mar -> 2
   | Mer -> 3
   | Gio -> 4
   | Ven -> 5
   | Sab -> 6
   | Dom -> 7 ;;




