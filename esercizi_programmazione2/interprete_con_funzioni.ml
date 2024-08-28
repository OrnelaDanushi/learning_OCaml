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
  (* fib usa sub2, funzione definita dopo *)
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

                                                    (* estensione di ambiente *)
let ext env (x: string) v = fun y -> if x=y then v else env y ;;
(* let ext env (x: string) (v) (y: string ) if x = y then v else env y ;; *)

(*
env, fenv : 'a -> 'b
ext : ('a -> 'b) -> 'a -> 'b -> 'a -> 'b
env : string -> int
fenv : string -> (string * exp)
*)

(* valutazione di espressioni  NB: booleani rappresentati da 0 e 1*)
let rec eval (e: exp) env fenv = match e with  
  | EInt i -> i
  | Den s -> env s
  | App(s,e2) -> let (par,body) = (fenv s) in (eval body (ext env par (eval e2 env fenv)) fenv)
  | Add (e1,e2) -> (eval e1 env fenv)+(eval e2 env fenv)
  | Sub (e1,e2) -> (eval e1 env fenv)-(eval e2 env fenv)
  | Mul (e1,e2) -> (eval e1 env fenv)*(eval e2 env fenv)
  | Not e1 -> if ((eval e1 env fenv) = 0) then 1 else 0
  | Or (e1,e2) -> if (eval e1 env fenv) = 0 then (eval e2 env fenv) else 1
  | And (e1,e2) -> if (eval e1 env fenv) != 0 then (eval e2 env fenv) else 0
  | Eq (e1,e2) -> if ((eval e1 env fenv) = (eval e2 env fenv)) then 1 else 0
  | Leq (e1,e2) -> if ((eval e1 env fenv) <= (eval e2 env fenv)) then 1 else 0
  | Ifz (e1,e2,e3) -> if (eval e1 env fenv) = 1 then (eval e2 env fenv)
  else (eval e3 env fenv) ;;

(* valutazione di dichiarazione: restituisce un ambiente globale *)
let rec dval (decls: def list) = match decls with
  | [ ] -> fenv0
  | Fun (fname, par, body)::rest -> ext (dval rest) fname (par, body) ;;

(* valutazione di programma: 
valuta l'espressione usando l'ambiente globale ottenuto dalle dichiarazioni *)
let peval (p: prog) = match p with
  Prog (decls, expr) -> let fenv = dval(decls) in eval expr env0 fenv;;

(* ============================= TESTS ================= *)
let p1 = Prog ([ ], Add(EInt 4, EInt 5));;
peval p1;;                                        (* basico: no funzioni *)

let p2 = Prog ([Fun("succ", "x", Add(Den "x", EInt 1))], Add(App("succ", EInt 4), EInt 5));;
peval p2;;                                        (* una funzione non ricorsiva: succ *)

let p3 = Prog (
[Fun("tria", "x", Ifz(Eq(Den "x", EInt 0), EInt 5, Add(Den "x", App("tria", Sub(Den "x", EInt
1)))))], App("tria", EInt 4));;
peval p3;;                                        (* funzione ricorsiva: triangolare *)

let p4 = Prog ([Fun("fact", "x", Ifz(Leq(Den "x", EInt 1), EInt 1, Mul(Den "x", App("fact",
Sub(Den "x", EInt 1)))))], App("fact", EInt 3));;
peval p4;;                                        (* funzione ricorsiva: fattoriale *)

let ptest =
Prog
([Fun ("sub1", "n", Sub(Den "n", EInt 1));
Fun ("fib", "n",
Ifz(Or(Eq(Den "n", EInt 0), Eq(Den "n", EInt 1)), Den "n",
Add(App("fib", App("sub1", Den "n")),
App("fib", App("sub2", Den "n")))));
Fun ("sub2", "m", Sub(Den "m", EInt 2))],
App("fib", EInt 5));;
peval ptest;; (* risultato: 5 *)










