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

type exp =                   (* vecchio interprete *)
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

type staticexp =             (* nuovo interprete *)
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
E' necessario ricostruire la struttura degli ambienti tramite newframes
  per tradurre correttamente i Den ide in accessi.
*)

let newframes(e, rho) = 
  let cframe = emptystack(cframesize(e), Expr1(e))
  let tframe = emptystack(tframesize(e), SUnbound)
  push(Expr1(e), cframe) 
  push(cframe, cstack) 
  push(tframe, tempsexpstack) 
  pushenv(rho)

(* traduttore *)
let bind ((r: evalenv), i, d) = ...
let bindlist (r, il, el) = ...
let pushargs ((b: exp list), continuation) = ...
let getargs ((b: exp list), (tempstack: staticexp stack)) = ...

(* interprete *)
let bind2 ((r: evalenv), d) = ...
let bindlist2 (r, el) = ... 
let pushargs2 ((b: staticexp list), continuation) = ...
let getargs2 ((b: staticexp list), (tempstack: eval stack)) = ...


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
        newframes(e2,bind(rho, i, SUnbound)) 
          (* a tempo di traduzione non c'è bisogno dei valori memorizzati nella pila evalstack
          nel vecchio interprete si può costruire il nuovo frame con il binding solo dopo aver
            valutato Expr(e1), cioè nella seconda fase della traduzione
          nel nuovo interprete, quindi qui, si anticipa alla prima fase la creazione del frame,
            inserendo nel campo valore un SUnbound
          *)
      | Fun(i, a) ->
        let foo = List.init (List.length i) (fun _ -> Unbound)
          (*ignoriamo i valori dei parametri, usiamo una lista dummy*)
        newframes(a,bindlist(rho, i, foo))
          (*prima di chiudere la funzione in una espressione statica
          valutare il corpo in un nuovo frame*)
      | Rec(f, e) ->
        newframes(e,bind(rho, f, Unbound))
          (* i costrutti Rec sono sempre nella forma 
          Let (ide, (Rec (ide, Fun(... )), ...))
          Bisogna creare un nuovo frame con il binding della funzione ricorsiva,
          Successivamente il costrutto Fun costruira' un nuovo frame 
            contenente i parametri della funzione.
          Prima di fare la chiusura per il costrutto Rec (verra' fatto nel ramo Exp2)
            bisogna valutare il corpo per effettuare eventuali traduzioni.
          *)
  | Expr2(x) ->
    pop(continuation)
    match x with
      | Eint(n) -> push(SInt(n), tempstack)     (* adesso tempstack e' una pila di stacexp*)
      | Ebool(b) -> push(SBool(b), tempstack)
      | Den(i) -> 
        (*
        push(applyenv(rho, i), tempstack)  ----> tradotto in Access(int, int) 
        la applyenv del vecchio interprete resituisce il valore alla locazione di ide
        nel caso del problema, interessa memorizzare i due offset accesses ed index
        non restituiamo percio' un eval ma un staticexp Access(x, y)
        dato che non interessa il valore memorizzato, 
          la pila evalstack risulta inutile
        restituire una chiusura lessicale contenente gli offset nella pila 
          dell'ambiente per prelevare il valore a runtime
        il nuovo interprete non ha bisogno di effettuare la ricerca per nome,
          la pila namestack diventa inutile
        *)
        
        let applyenv ((x: evalenv), (y: ide)) = 
          let n = ref(x)
          let found = ref(false)
          let accesses = ref 0
          let index = ref 0
          while not !found && !n > -1 do
            let lenv = access(namestack, !n)
            let n1 = Array.length lenv
            index := 0
            while not !found && !index < n1 do
              if Array.get lenv !index = y then
                found := true
              else 
                index := !index + 1
              done
              if not !found then
                n := access(slinkstack, !n)
                accesses := !accesses + 1
            done
            if !found then
              Access(!accesses, !index)
            else
              SUnbound
      | Iszero(a) -> 
        let arg = top(tempstack)
        pop(tempstack)
        push(Siszero(arg), tempstack) 
      | Eq(a, b) ->
        let firstarg = top(tempstack)
        pop(tempstack)
        let sndarg = top(tempstack)
        pop(tempstack)      
        push(Sequ(firstarg, sndarg), tempstack) 
      | Prod(a, b) ->
        let firstarg = top(tempstack)
        pop(tempstack)
        let sndarg = top(tempstack)
        pop(tempstack)      
        push(Smult(firstarg, sndarg), tempstack) 
      | Sum(a, b) ->
        let firstarg = top(tempstack)
        pop(tempstack)
        let sndarg = top(tempstack)
        pop(tempstack)      
        push(Splus(firstarg, sndarg), tempstack) 
      | Diff(a, b) ->
        let firstarg = top(tempstack)
        pop(tempstack)
        let sndarg = top(tempstack)
        pop(tempstack)      
        push(Sdiff(firstarg, sndarg), tempstack) 
      | Minus(a) -> 
        let arg = top(tempstack)
        pop(tempstack)
        push(Sminus(arg), tempstack) 
      | And(a, b) ->
        let firstarg = top(tempstack)
        pop(tempstack)
        let sndarg = top(tempstack)
        pop(tempstack)      
        push(Set(firstarg, sndarg), tempstack) 
      | Or(a, b) ->
        let firstarg = top(tempstack)
        pop(tempstack)
        let sndarg = top(tempstack)
        pop(tempstack)      
        push(Svel(firstarg, sndarg), tempstack) 
      | Not(a) -> 
        let arg = top(tempstack)
        pop(tempstack)
        push(Snon(arg), tempstack) 
      | Ifthenelse(a, b, c) -> 
        let firstarg = top(tempstack)
        pop(tempstack)
        let sndarg = top(tempstack)
        pop(tempstack)      
        let trdarg = top(tempstack)
        pop(tempstack)      
        push(Sifthenelse(firstarg, sndarg, trdarg), tempstack) 

      | Appl(a, b) ->
        let firstarg = top(tempstack)
        pop(tempstack)
        let sndarg = top(tempstack)
        pop(tempstack)      
        push(SAppl(firstarg, sndarg), tempstack) 

      | Let(i, e1, e2) ->
        let firstarg = top(tempstack)
        pop(tempstack)
        let sndarg = top(tempstack)
        pop(tempstack)      
        push(SBind(firstarg, sndarg), tempstack) 

      | Fun(i, a) ->
        let arg = top(tempstack)
        pop(tempstack)
        push(SFun(arg), tempstack) 
      | Rec(f, e) ->
        let arg = top(tempstack)
        pop(tempstack)
        push(SRec(arg), tempstack) 

      (* una volta tradotte le sottoespressioni in ambienti con i binding effettuati correttamente,
      e' possibile chiudere lessicalmente i costrutti
      *)

      done
      let valore = top(top(tempsexpstack))
      pop(top(tempsexpstack))
      pop(cstack)
      pop(tempsexpstack)
      push(valore, top(tempsexpstack))
      popenv()
    done
    let valore = top(top(tempsexpstack))
    pop(tempsexpstack)
    valore

    (* al termine della traduzione, come nel vecchio interprete,
      restituire il valore presente nella pila temporanea
    che nel caso del problme non è un eval
    ma una espressione statica contenente tutto l'albero di sintassi astratta del programma in input
    dove avremo tradotto tutti i costrutti in costrutti alternativi senza ide
    e tutti i Den(ide) in Access(int, int)
    il codice prodotto può essere adesso dato in input al nuovo interprete
    
    
    e la retention? nessuna
    e' necessario farla quando una espressione valuta un Funval(Fun(ii, aa), r)
    se si fa popenv l'ambiente r non esiste più al momento dell'applicazione,
      e il valore relativo di slinkstack sarà compromesso
    # sem(
      Appl(Appl(Fun(["x"], Fun(["y"], Sum(Den("x", Den("y")))), [Eint 3]), [Eint 5])),
      emptyenv Unbound);;

    durante l'analisi statica interessa soltanto tradurre i nomi
    perciò, quando si incontra un Fun(i, exp) 
      pushiamo un frame per exp
      e valutiamo eventuali identificatori interni
      es: Fun(["y"], Sum(Den("x"), Den("y")))
    quando applicheremo la funzione costruiremo semplicemente una chiusura lessicale:
      Sappl(firstarg, sndarg)
    l'argomento di Sappl sono le espressioni statiche con i nomi tradotti
    non applichiamo mai, non avremo nessun problema di retention
    *)

(*

Il nuovo interprete prende in input il codice valutato parzialmente (valori di tipo staticexp),
  e accede direttamente alla pila di ambienti evalstack 
  senza cercare il nome nella pila parallela namestack (valuta ad eval).
Bisogna "duplicare" alcuni metodi usati dal traduttore in quanto cambiano i tipi:
  vecchio interprete: exp -> eval
  traduttore: exp -> staticexp
  nuovo interpret: staticexp -> eval
Alternativamente usare le funzioni polimorfe

Soluzione scelta (più semplice): 
2 pile 
  cstack (di tipo exp nel traduttore, staticexp nell'interprete) 
  tempstack (di tipo staticexp nel traduttore, eval nell'interprete) 
duplicati i metodi 
  bind, bindlist 
    hanno un numero diverso di parametri, 
    nel traduttore ci sono gli identificatori, nell'interprete no
  pushargs, getargs (prendono exp nel traduttore, staticexp nell'interprete)
il dominio efun adesso usa staticexp per le chiusure lessicali
  | SFun(a) -> push(makefun(SFun(a), rho), tempstack)
*)

let makefun ((a:staticexp), (x:evalenv)) =
  match a with 
    | SFun(aa) -> Funval(a, x)
    | _ -> failwith ("Non-functional object")
    and eval = 
      | Int of int
      | Bool of bool
      | Unbound
      | Funval of efun
      and efun = staticexp * (evalenv)

(* non cambia niente rispetto al vecchio interprete
c'è solamente staticexp invece di exp *)
match top (continuation) with
  | SExpr1(x) ->
    pop(continuation)
    push(SExpr2(x), continuation)
    match x with
      | Siszero(a) -> push(SExpr1(a), continuation) 
      | Sequ(a, b) ->
        push(SExpr1(a), continuation) 
        push(SExpr1(b), continuation) 
      | Smult(a, b) ->
        push(SExpr1(a), continuation) 
        push(SExpr1(b), continuation) 
      | Splus(a, b) ->
        push(SExpr1(a), continuation) 
        push(SExpr1(b), continuation) 
      | Sdiff(a, b) ->
        push(SExpr1(a), continuation) 
        push(SExpr1(b), continuation) 
      | Sminus(a) -> push(SExpr1(a), continuation) 
      | Set(a, b) ->
        push(SExpr1(a), continuation) 
        push(SExpr1(b), continuation) 
      | Svel(a, b) ->
        push(SExpr1(a), continuation) 
        push(SExpr1(b), continuation) 
      | Snon(a) -> push(SExpr1(a), continuation) 
      | Sifthenelse(a, b, c) -> 
        push(SExpr1(a), continuation) 
        push(SExpr1(b), continuation) 
        push(SExpr1(c), continuation) 
      | SBind(e1, e2) -> push(SExpr1(e1), continuation)
      | SAppl(a, b) ->
        push(SExpr1(a), continuation) 
        pushargs2(b, continuation) 
      | _ -> ()

  | Expr2(x) ->
    pop(continuation)
    match x with
      | SUnbound -> push(Unbound, tempstack)
      | SInt(n) -> push(Int(n), tempstack)     
      | SBool(b) -> push(Bool(b), tempstack)
      | Siszero(a) -> 
        let arg = top(tempstack)
        pop(tempstack)
        push(iszero(arg), tempstack) 
      | Sequ(a, b) ->
        let firstarg = top(tempstack)
        pop(tempstack)
        let sndarg = top(tempstack)
        pop(tempstack)      
        push(equ(firstarg, sndarg), tempstack) 
      | Smult(a, b) ->
        let firstarg = top(tempstack)
        pop(tempstack)
        let sndarg = top(tempstack)
        pop(tempstack)      
        push(mult(firstarg, sndarg), tempstack) 
      | Splus(a, b) ->
        let firstarg = top(tempstack)
        pop(tempstack)
        let sndarg = top(tempstack)
        pop(tempstack)      
        push(plus(firstarg, sndarg), tempstack) 
      | Sdiff(a, b) ->
        let firstarg = top(tempstack)
        pop(tempstack)
        let sndarg = top(tempstack)
        pop(tempstack)      
        push(diff(firstarg, sndarg), tempstack) 
      | Sminus(a) -> 
        let arg = top(tempstack)
        pop(tempstack)
        push(minus(arg), tempstack) 
      | Set(a, b) ->
        let firstarg = top(tempstack)
        pop(tempstack)
        let sndarg = top(tempstack)
        pop(tempstack)      
        push(et(firstarg, sndarg), tempstack) 
      | Svel(a, b) ->
        let firstarg = top(tempstack)
        pop(tempstack)
        let sndarg = top(tempstack)
        pop(tempstack)      
        push(vel(firstarg, sndarg), tempstack) 
      | Snon(a) -> 
        let arg = top(tempstack)
        pop(tempstack)
        push(non(arg), tempstack) 
      | Sifthenelse(a, b, c) -> 
        let arg = top(tempstack)
        pop(tempstack)
        match arg with with
          | Bool (bg) ->
            if bg then
              push(SExpr1(b), continuation)
            else
              push(SExpr1(c), continuation)
          | _ -> failwith ("type error")

      (* fino qui e' tutto come il vecchio interprete
      ad eccezione delle staticexp *)

  | Access(l, i) -> push(accessenv(rho, l, i), tempstack)
    let accessenv ((x: evalenv), (l: int), (index: int)) = 
      let l = ref(l)
      let n = ref(x)
      while !l > 0 do
        n := access(slinkstack, !n)
        l := !l - 1
      Array.get (access(evalstack, !n)) index

    (* qui non c'è Den(ide) ma Access(int, int)
    non si esegue piu' una ricerca del nome nella pila degli ambienti,
    ma accediamo direttamente
    abbiamo eliminato un ciclo ed un confronto tra stringhe ad ogni iterazione del ciclo,
      risparmiando anche nell strutture dati (la pila namestack è inutile)
    scorriamo la catena statica con slinkstack fino all'ambiente dove si trova il valore cercato
    dopo con Array.get restituiamo l'eval che corrispondeva all'ide tradotta
    *)
 | SFun(a) ->    
  

(*
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

