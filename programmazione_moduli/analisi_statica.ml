(* TRADUZIONE DEI NOMI TRAMITE LA STRUTTURA STATICA

Problema 
Dato il programma, per tradurre una specifica occorrenza di Den ide occorre:
- identificare la struttura di annidamento,
- identificare il blocco o funzione dove occorre l'associazione per ide (o scoprire subito che non c'è)
  e vedere in che posizione è ide nell'ambiente,
- contare la differenza delle profondità di nesting.

Soluzione
In maniera simile ad usare un valutatore parziale, costruire un'analisi statica.
Sostituire il vecchio interprete da un traduttore ed un interprete.
*)

type exp = 
  | Eint of int
  | Ebool of bool
  | Den of ide
  | Prod of exp * exp
  | Sum of exp * exp
  | Diff of exp * exp
  | Eq of exp * exp
  | Minus of exp 
  | Iszero of exp 
  | or of exp * exp
  | And of exp * exp
  | Not of exp 
  | Ifthenelse of exp * exp * exp
  | Let of ide * exp * exp
  | Fun of ide list * exp
  | Appl of exp * exp list
  | Rec of ide * exp

type staticexp = 
  | SUnbound
  | SInt of int
  | SBool of bool
  | Access of int * int
  | Smult of staticexp * staticexp
  | Splus of staticexp * staticexp
  | Sdiff of staticexp * staticexp
  | Sequ of staticexp * staticexp
  | Sminus of staticexp 
  | Siszero of staticexp 
  | Svel of staticexp * staticexp
  | Set of staticexp * staticexp
  | Snon of staticexp 
  | Sifthenelse of staticexp * staticexp * staticexp
  | SBind of staticexp * staticexp
  | SFun of staticexp
  | SAppl of staticexp * staticexp list
  | SRec of staticexp

(*

Il traduttore valuta parzialmente il programma in input, 
  e produce un altro programma con tutti i nomi sostituiti dall'offset seguendo la catena statica.

*)

match top (continuation) with
  | Expr1(x) ->
    pop(continuation)
    push(Expr2(x), continuation)
    match x with
      | Iszero(a) -> push(Expr1(a), continuation) 
      | Eq(a, b) ->
        push(Expr1(a), continuation) 
        push(Expr1(b), continuation) 
      | Prod(a, b) ->
        push(Expr1(a), continuation) 
        push(Expr1(b), continuation) 
      | Sum(a, b) ->
        push(Expr1(a), continuation) 
        push(Expr1(b), continuation) 
      | Diff(a, b) ->
        push(Expr1(a), continuation) 
        push(Expr1(b), continuation) 
      | Minus(a) -> push(Expr1(a), continuation) 
      | And(a, b) ->
        push(Expr1(a), continuation) 
        push(Expr1(b), continuation) 
      | Or(a, b) ->
        push(Expr1(a), continuation) 
        push(Expr1(b), continuation) 
      | Not(a) -> push(Expr1(a), continuation) 
      | Ifthenelse(a, b, c) -> 
        (* staticamente eseguiamo entrambi i rami dell'if per tradurre i Den(i) interni *)
        push(Expr1(a), continuation) 
        push(Expr1(b), continuation) 
        push(Expr1(c), continuation) 
      | Appl(a, b) ->
        push(Expr1(a), continuation) 
        pushargs(b, continuation) 
      | Let(i, e1, e2) ->
        push(Expr1(e1), continuation) 
          (* prima di chiudere la funzione in una espressione statica
          valutare il corpo in un nuovo frame*)
        newframes(e2,bind(rho, i, SUnbound) 
      | Fun(i, a) ->
        let foo = List.init (List.length i) (fun _ -> Unbound)
          (*ignoriamo i valori dei parametri, usiamo una lista dummy*)
        newframes(a,bindlist(rho, i, foo)
          (*prima di chiudere la funzione in una espressione statica
          valutare il corpo in un nuovo frame*)
      | Rec(f, e) ->
        newframes(e,bind(rho, f, Unbound)
          (* i costrutti Rec sono sempre nella forma 
          Let (ide, (Rec (ide, Fun(... )), ...))
          Bisogna creare un nuovo frame con il binding della funzione ricorsiva,
          Successivamente il costrutto Fun costruira' un nuovo frame 
            contenente i parametri della funzione.
          Prima di fare la chiusura per il costrutto Rec (verra' fatto nel ramo Exp2)
            bisogna valutare il corpo per effettuare eventuali traduzioni.
          *)







(*

Il nuovo interprete prende in input il codice valutato parzialmente,
  e accede direttamente alla pila di ambienti evalstack 
  senza cercare il nome nella pila parallela namestack.

Eseguire il programma con l'interprete sui costrutti solo dell'ambiente (ignorando tutti gli altri), 
  e cioè che guardi solo i nomi (namestack) e link (slinkstack) statici.
Costruire un nuovo ambiente locale seguendo la struttura statica (Let, Fun, Rec)
  e non quella dinamica (Let, Apply)
  facendo attenzione ad associare ad ogni espressione l'ambiente in cui deve essere valutata.
Tale costruzione dell'ambiente è diversa da quella a tempo d'esecuzione basata sulle applicazioni
  e non sulle definizioni di funzione.
*)

(*es: input traduttore che prende in input una espressione*)
val expo : exp = 
Let (
  "expo", 
  Rec(
    "expo", 
    Fun(
      ["base"; "esp"], 
      Let(
        "f", 
        Fun(
          ["x"], 
          Ifthenelse (Iszero (Den "esp"), Appl (Den "f", [Eint 1]), Prod (Den "x", Appl (Den "expo", [Den "x"; Diff (Den "esp", Eint 1)])))),
        Appl (Den "f", [Den "base"])))),
  Appl (Den "expo", [Den "x"; Eint 3]))

(* es: output traduttore
il compilatore restituisce una nuova espressione di tipo staticexp
i nomi sono scomparsi
i Den ide sono stati tradotti in: 
  Access(int, int) se il nome esisteva nella catena statica
  Sunbound se il nome non era visibile nella catena statica

> val it : staticexp = 
SBind
  (SRec (SFun (SBind (SFun (
    Sifthenelse (
      Siszero (
        Access (1, 1)), 
        SAppl (SUnbound, [SInt 1]),
        Smult (Access (0, 0), SAppl (Access (2, 0), [Access (0, 0); Sdiff(Access (1, 1), SInt 1)])))),
      SAppl (Access (0, 0), [Access (1, 0)])))),
  SAppl (Access (0, 0), [SUnbound; SInt 3]))
*)

