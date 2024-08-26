(* TRADUZIONE DEI NOMI TRAMITE LA STRUTTURA STATICA

Problema 
Dato il programma, per tradurre una specifica occorrenza di Den ide occorre:
- identificare la struttura di annidamento,
- identificare il blocco o funzione dove occorre l'associazione per ide (o scoprire subito che non c'è)
  e vedere in che posizione è ide nell'ambiente,
- contare la differenza delle profondità di nesting.

Soluzione
In maniera simile ad usare un valutatore parziale, costruire un'analisi statica.
1) Definire l'interprete.
Eseguire il programma con l'interprete sui costrutti solo dell'ambiente (ignorando tutti gli altri), 
  e cioè che guardi solo i nomi (namestack) e link (slinkstack) statici.
Costruire un nuovo ambiente locale seguendo la struttura statica (Let, Fun, Rec)
  e non quella dinamica (Let, Apply)
  facendo attenzione ad associare ad ogni espressione l'ambiente in cui deve essere valutata.
Tale costruzione dell'ambiente è diversa da quella a tempo d'esecuzione basata sulle applicazioni
  e non sulle definizioni di funzione.

1) Interprete
Sostituire il vecchio interprete da un traduttore ed un interprete.
Il traduttore valuta parzialmente il programma in input, 
  e produce un altro programma con tutti i nomi sostituiti dall'offset seguendo la catena statica.
Il nuovo interprete prende in input il codice valutato parzialmente,
  e accede direttamente alla pila di ambienti evalstack 
  senza cercare il nome nella pila parallela namestack.
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

