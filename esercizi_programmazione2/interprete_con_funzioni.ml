(*
Grammatica che definisce un linguaggio funzionale semplice

Program Decl => Exp                               programma
Decl ::= epsilon | fun Ide(Ide) {Exp} ; Decl      dichiarazioni
Ide ::= <def>                                     identificatori
Int ::= int                                       interi
Bool ::= true | false                             booleani
Op ::= + | - | * | = | < | <= | > | >=            operatori
Exp ::=                                           espressioni
  | Ide
  | Int
  | Bool
  | Exp and Exp
  | Exp or Exp
  | not Exp
  | Op (Exp, Exp)
  | if Exp then Exp else Exp
  | Ide (Exp)

fun f (x) {expr}                                dichiarazione di funzione
  f = nome della funzione
  x = parametro formale
  expr = espressione dove x può comparire libera
come in C, le dichiarazioni di funzione occorrono solo al "top-level" 
  e definiscono un ambiente globale nel quale deve essere valutata 
  l'espressione finale del programma


Definire una semantica operazionale mediante regole di inferenza che rispetti
- l'applicazione funzionale valutata con riferimento all'ambiente globale
  determinato dalle dichiarazioni
- tutte le altre operazioni hanno il significato opportuno

Verificare la correttezza di tale semantica progettando ed eseguendo casi di test,
sufficienti a testare tutti gli operatori.
In particolare, valutare il programma con risultato 5

Program fib(5)
fun sub1 (n) {-(n, 1)};
fun fib (n) { if =(n,0) then n else + (fib (sub1(n)), fib (sub2(n)))};
fun sub2 (m) { sub1 (sub1(m))}; epsilon

Definire una sintassi astratta per il linguaggio, con opportuni tipi di dato
Definire un interprete che corrisponda a tale sintassi
Tradurre nella sintassi i casi di test proposti prima,
  in particolare il Program indicato, e valutarlo con l'interprete.
*)

type ide = string ;;

type exp =                                         
  | Den of ide
  | EInt of int
  | Add of exp * exp
  | Sub of exp * exp
  | Mul of exp * exp
  | Add of exp * exp
  | Eq of exp * exp
  | Leq of exp * exp
  | Not of exp 
  | And of exp * exp
  | Or of exp * exp
  | Ifz of exp * exp * exp
  | App of ide * exp
;;

type def = Fun of ide * ide * exp ;;

type prog = Prog of (def list) * exp ;;


(*
a runtime ci sono due possibilità per l'ambiente
- uno solo, contenente sia funzioni globali che identificatori associati ad interi
  per semplicità non ci sono i booleani,
  introdotti per passaggio di parametri
- due ambienti separati, uno globale per le funzioni, uno locale per gli identificatori
  soluzione adottata
  nell'ambiente globale si associa al nome di una funzione una coppia : ide * exp
  l'ambiente globale e' gestito come se fosse scoping dinamico, 
  quindi passato all'invocazione,
  per garantire che contenga tutte le funzioni dichiarate
*)

let fenv0 = fun x -> raise EmptyEnv ;;              (* ambiente globale di default *)
(*oppure let fenv0 x = raise EmptyEnv ;; *)

let env0 = fenv0 ;;                                 (* ambiente locale di default *)

let ext env (x: string) v = fun y -> if x=y then v else env y ;;
(* let ext env (x: string) (v) (y: string ) if x = y then v else env y ;; *)


















