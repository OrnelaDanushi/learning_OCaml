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
- nel passaggio per nome
  l'espressione che rappresenta il parametro attuale della funzione chiamata deve
  essere valutata solo al momento nel quale il parametro formale è effettivamente 
  acceduto, e l'ambiente di valutazione deve essere quello definito al momento
  nel quale la funzione e' invocata
- nel passaggio per riferimento
  il parametro attuale della funzione chiamata deve essere una variabile 
  e deve conservare le eventuali modifiche anche dopo il termine della funzione
- tutte le altre operazioni abbiano il significato opportuno

Versione 2
- modificare la semantica in modo che se una funzione passa il proprio parametro
formale per riferimento, alla fine della chiamata il valore calcolato del corpo della funzione
viene assegnato al parametro attuale
es: restituire il valore 9.
Prog([ Var("base", EInt 1);
    Fun("iden", Val "n", Den "n");
    Fun("inc", Ref "n", Add(Den "n", EInt 1));
    Var("test", Add(App("inc", Den "base"), Den "base"))
  ],App("iden", Add(Den "test", App("inc", Den "test"))))


Verificare la correttezza di tale semantica progettando ed eseguendo casi di test,
sufficienti a testare tutti gli operatori.

Definire una sintassi astratta per il linguaggio, con opportuni tipi di dato
Definire un interprete che corrisponda a tale sintassi
Tradurre nella sintassi i casi di test proposti prima,
  (in particolare il Program indicato) 
  e valutarli con l'interprete.
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

(* includere la possibilità di passare il parametro alle funzioni sia per nome che per riferimento *)
type loc = int ;;
type param = Val of ide | Name of ide | Ref of ide ;;
type venv = ide -> evT and evT = Unbound | Loc of loc | ExpVal of exp * venv ;;
type dvT = Undef | FunVal of param * exp * venv ;;
type mvT = int ;;
type denv = ide -> dvT ;;
type store = loc -> mvT ;;
type def = Var of ide * exp | Fun of ide * param * exp ;;
type prog = Prog of (def list) * exp ;;

exception EmptyEnv ;;                      (* eccezioni *)
exception WrongFun ;;

(* a runtime ci sono due possibilità per l'ambiente
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



(* es 7bis*)


(*
env, fenv : 'a -> 'b
ext : ('a -> 'b) -> 'a -> 'b -> 'a -> 'b
env : string -> int
fenv : string -> (string * exp)
*)

(* Contatore di locazioni: e' un puntatore!! *)
(* la presenza di s e' concettuale: la newloc dovrebbe dipendere dallo store... *)
let count = ref 0 ;;
let newloc (s: store) = (incr count; !count);;

let rec lval (e: exp) (r: venv) (g: denv) (s: store) : evT = match e with
  | Den id -> r id
  | _ -> let tmp = (newloc s) in Loc tmp;;


(* valutazione a runtime di espressioni  NB: booleani rappresentati da 0 e 1*)
(*
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
*)

let rec eval (e : exp) (r : venv) (g : denv) (s : store) : mvT = match e with
  | EInt i -> i
  | Den id -> let vClosure = (r id) in (match vClosure with
    | Loc lo -> s lo
    | ExpVal(e1, r1) -> eval e1 r1 g s
    | _ -> raise EmptyEnv)
  | App (f, arg) -> let fClosure = (g f) in (match fClosure with
    | FunVal(par, fBody, fDecEnv) -> auxval fClosure arg r g s
    | _ -> raise WrongFun)
  | Add (e1,e2) -> (eval e1 r g s)+(eval e2 r g s)
  | Sub (e1,e2) -> (eval e1 r g s)-(eval e2 r g s)
  | Mul (e1,e2) -> (eval e1 r g s)*(eval e2 r g s)
  | Not e1 -> if ((eval e1 r g s) = 0) then 1 else 0
  | Or (e1,e2) -> if (eval e1 r g s) = 0 then (eval e2 r g s) else 1
  | And (e1,e2) -> if (eval e1 r g s) != 0 then (eval e2 r g s) else 0
  | Eq (e1,e2) -> if ((eval e1 r g s) = (eval e2 r g s)) then 1 else 0
  | Leq (e1,e2) -> if ((eval e1 r g s) <= (eval e2 r g s)) then 1 else 0
  | Ifz (e1,e2,e3) -> if (eval e1 r g s) = 1 then (eval e2 r g s)
                      else (eval e3 r g s)

  (* valutazione di funzioni: restituisce un valore *)
  and auxval (fClos : dvT) (arg : exp) (r : venv) (g : denv) (s : store) : mvT = match fClos with
    | FunVal(par, fBody, fDecEnv) -> (match par with
      | Val id -> let tmp = (newloc s) in
        let v = (eval arg r g s) in
        eval fBody (bind fDecEnv id (Loc tmp)) g (bind s tmp v)
      | Name id -> let tmp = (ExpVal(arg, r)) in
        eval fBody (bind fDecEnv id tmp) g s
      | (* si passa l'ambiente al momento della chiamata di funzione *)
      Ref id -> let tmp = (lval arg r g s) in (match tmp with
        | Loc lo -> eval fBody (bind fDecEnv id tmp) g s
        | (* se e' una locazione nuova, lo e' indefinito in s *)
        | _ -> failwith("RefPar error") ) )
      | _ -> raise WrongFun

  (* valutazione di dichiarazioni: restituisce un ambiente globale *)
  and dval decls (r : venv) (g : denv) (s : store) : venv * denv * store = match decls with
    | [ ] -> (r, g, s)
    | Fun(fname, par, body)::rest ->
      let g1 = (bind g fname (FunVal(par, body, r))) in dval rest r g1 s
    | Var(vid, e1)::rest -> let v = (eval e1 r g s) in
      let tmp = (newloc s) in
      let r1 = (bind r vid (Loc tmp)) in
      let s1 = (bind s tmp v) in
      dval rest r1 g s1 ;;

(* Fun("sub1", Val "n", Sub(Den "n", Den "base1")) *)

(*
(* valutazione di dichiarazione: restituisce un ambiente globale *)
let rec dval (decls: def list) = match decls with
  | [ ] -> fenv0
  | Fun (fname, par, body)::rest -> ext (dval rest) fname (par, body) ;;

(* valutazione di programma: 
valuta l'espressione usando l'ambiente globale ottenuto dalle dichiarazioni *)
let peval (p: prog) = match p with
  Prog (decls, expr) -> let fenv = dval(decls) in eval expr env0 fenv;;
*)

let pval p = match p with
Prog(decls, e) ->
let (venv, denv, store) = (dval decls env0 env0 env0) in (eval e venv denv store) ;;

(* ============================= TESTS ================= *)
let p1 = Prog ([ ], Add(EInt 4, EInt 5));;
peval p1;;                                        (* basico: no funzioni *)

let p2 = Prog ([Fun("succ", "x", Add(Den "x", EInt 1))], Add(App("succ", EInt 4), EInt 5));;
peval p2;;                                        (* una funzione non ricorsiva: succ *)
(* restituisce - : mvT = 10, lo stesso con Name "x", mentre con Ref "x" avrebbe
lanciato Exception: EmptyEnv *)

let p3 = Prog (
  [Fun("tria", "x", Ifz(Eq(Den "x", EInt 0), EInt 5, Add(Den "x", App("tria", Sub(Den "x", EInt
1)))))], App("tria", EInt 4));;
peval p3;;                                        (* funzione ricorsiva: triangolare *)

let p4 = Prog ([Fun("fact", "x", Ifz(Leq(Den "x", EInt 1), EInt 1, Mul(Den "x", App("fact",
Sub(Den "x", EInt 1)))))], App("fact", EInt 3));;
(* let p4 = Prog([Var("test", EInt 3); Fun("fact", Val "x", Ifz(Leq(Den "x", EInt 1), EInt 1,
Mul(Den "x", App("fact", Sub(Den "x", EInt 1)))))],
App("fact", Den "test"));; *)
peval p4;;                                        (* funzione ricorsiva: fattoriale *)

(*
fun sub1 (n) {-(n, 1)};
fun fib (n) { if =(n,0) then n else + (fib (sub1(n)), fib (sub2(n)))};
  (* fib usa sub2, funzione definita dopo *)
fun sub2 (m) { sub1 (sub1(m))}; epsilon

let ptest = Prog 
([Fun ("sub1", "n", Sub(Den "n", EInt 1));
  Fun ("fib", "n",
  Ifz(Or(Eq(Den "n", EInt 0), Eq(Den "n", EInt 1)), Den "n",
  Add(App("fib", App("sub1", Den "n")),
  App("fib", App("sub2", Den "n")))));
  Fun ("sub2", "m", Sub(Den "m", EInt 2))],
  App("fib", EInt 5));;

peval ptest;; (* risultato: 5 *)

*)

(*
var base0 { 0 }; va base1 { 1 };
fun sub1 (m) { m - base1 };
fun fib (n) { if =(n, base0) or =(n, base1) then n else +(fib(sub1(n)), fib (sub2(n)))};
fun sub2 (m) { sub1(sub1(m)) };
var add { 3 };
var test { base1 + add };
var add { 5 } &epsilon;
*)

let ptest =
  Prog([Var("base0", EInt 0); Var("base1", EInt 1);
  Fun("sub1", Val "n", Sub(Den "n", Den "base1"));
  Fun("fib", Val "n",
  Ifz(Or(Eq(Den "n", Den "base0"), Eq(Den "n", Den "base1")), Den "n",
  Add(App("fib", App("sub1", Den "n")),
  App("fib", App("sub2", Den "n")))));
  Fun("sub2", Val "m", Sub(Sub(Den "m", Den "base1"), Den "base1"));
  Fun ("inc", Ref "n", Add(Den "n", Den "base1"));
  Var("base", EInt 3);
  Var("test", Add(App("inc", Den "base"), Den "base"))],
  App("fib", Den "test")) ;;

pval ptest;; (* risultato: 13 *)

(* ============================= TESTS ================= *)

(* SECONDA VERSIONE *)

type 't env = ide -> 't ;;                        (* Ambiente polimorfo*)

                                                  (* Estensione di ambiente *)
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else r x;;
(* oppure let bind (r: 't env)(i: ide)(v: 't)(x: ide) = if x = i then v else r x ;; *)

exception EmptyEnv;;
exception WrongFun;;

let env0 = fun x -> raise EmptyEnv ;;            (* Ambiente default *)
(* oppure let env0 x = raise EmptyEnv ;; *)

(*
bind : ('a -> 'b) -> 'a -> 'b -> 'a -> 'b
venv = int env
fenv = (ide * exp) env
*)

let rec eval e venv denv = match e with
  | EInt i -> i
  | Den s -> venv s
  | App (s, e1) -> (match (denv s) with
    (par, body) -> let v = (eval e1 venv denv) in
      let venv1 = (bind venv par v) in
        let venv1 = (bind env0 par v) in (* cosi' abbiamo scoping statico *)
          (* scoping dinamico con let venv1 = (bind venv par v) in *)
          eval body venv1 denv
      | _ -> raise WrongFun)
  | Add (e1,e2) -> (eval e1 venv denv)+(eval e2 venv denv)
  | Sub (e1,e2) -> (eval e1 venv denv)-(eval e2 venv denv)
  | Mul (e1,e2) -> (eval e1 venv denv)*(eval e2 venv denv)
  | Not e1 -> if ((eval e1 venv denv) = 0) then 1 else 0
  | Or (e1,e2) -> if (eval e1 venv denv) = 0 then (eval e2 venv denv) else 1
  | And (e1,e2) -> if (eval e1 venv denv) != 0 then (eval e2 venv denv) else 0
  | Eq (e1,e2) -> if ((eval e1 venv denv) = (eval e2 venv denv)) then 1 else 0
  | Leq (e1,e2) -> if ((eval e1 venv denv) <= (eval e2 venv denv)) then 1 else 0
  | Ifz (e1,e2,e3) -> if (eval e1 venv denv) = 1
                        then (eval e2 venv denv)
                        else (eval e3 venv denv)
;;

(* valutazione di dichiarazione: restituisce un ambiente globale *)
let rec dval (decls: def list) = match decls with
  | [ ] -> env0
  | Fun (fname, par, body)::rest -> bind (dval rest) fname (par, body) ;;

(* valutazione di programma: 
valuta l'espressione usando l'ambiente globale ottenuto dalle dichiarazioni *)
let pval (p: prog) = match p with
  Prog(decls, exp) -> let fenv = (dval decls) in eval exp env0 fenv;;

(* ============================= TESTS ================= *)

let p1 = Prog([ ], Add(EInt 4, EInt 5));;
pval p1;;                                        (* basico: no funzioni *)

let p2 = Prog([Fun("succ", "x", Add(Den "x", EInt 1))], Add(App("succ", EInt 4), EInt 5));;
pval p2;;                                        (* una funzione non ricorsiva: succ *)

let p3 = Prog([Fun("tria", "x", Ifz(Eq(Den "x", EInt 0), EInt 5, Add(Den "x", App("tria", 
  Sub(Den "x", EInt 1)))))], App("tria", EInt 4));;
pval p3;;                                        (* funzione ricorsiva: triangolare *)

let p4 = Prog([Fun("fact", "x", Ifz(Leq(Den "x", EInt 1), EInt 1, Mul(Den "x", App("fact",
  Sub(Den "x", EInt 1)))))], App("fact", EInt 3));
pval p4;;                                        (* funzione ricorsiva: fattoriale *)

let ptest = 
  Prog([Fun("sub1", "n", Sub(Den "n", EInt 1));
  Fun("fib", "n",
  Ifz(Or(Eq(Den "n", EInt 0), Eq(Den "n", EInt 1)), Den "n",
  Add(App("fib", App("sub1", Den "n")),
  App("fib", App("sub2", Den "n")))));
  Fun("sub2", "m", Sub(Den "m", EInt 2))],
  App("fib", EInt 4));;

pval ptest;; (* risultato: 3 *)













