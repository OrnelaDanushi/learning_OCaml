(* DEFINIZIONI *)
type ide = string;;
type exp =	Eint of int 	| Ebool of bool 	| Den of ide 	| Prod of exp * exp 
| Sum of exp * exp 	| Diff of exp * exp 	| Eq of exp * exp 
| Minus of exp 		| IsZero of exp 	| Or of exp*exp| And of exp*exp 
| Not of exp 		| Ifthenelse of exp * exp * exp 	| Let of ide * exp * exp 
| Fun of ide * exp 	| FunCall of exp * exp 	| Letrec of ide * exp * exp
| RecFun of ide * ide * exp

| Etree of tree (* gli alberi sono anche espressioni *)

(* ApplyOver(exf, ext): applica la funzione denotata dal primo parametro exf al valore associato ad ogni nodo dell’albero denotato dal secondo parametro ext, aggiornandolo di conseguenza. *)
| ApplyOver of exp * exp (* applicazione di funzione ai nodi *)

(* Update(idl, exf, ext) aggiorna solo il valore del nodo (o dei nodi) identificati dal cammino idl nell’albero ext applicando la funzione denotata da exf, mentre non esegue nessun aggiornamento se nessun nodo corrisponde al cammino indicato. *)
| Update of (ide list) * exp * exp (* aggiornamento di un nodo *)

(* Select(idl,exf, ext) restituisce un sotto-albero di ext la cui radice è uno dei nodi di ext che sono individuati dal cammino idl e il cui valore soddisfa la proprietà definita dalla funzione denotata da exf (funzione che restituisce un valore booleano). 
L’operazione Select restituisce l’albero vuoto se nessun nodo corrisponde al cammino indicato, oppure se nessun valore dei nodi corrispondenti al cammino soddisfa la condizione.
*)
| Select of (ide list) * exp * exp (* selezione condizionale di un nodo *)

and tree = Empty | Node of ide * exp * tree * tree	(* albero di espressioni *)
;;

(* funzione di ausilio per la costruzione di un albero di espressioni *)
let leaf (i : ide)(x : exp) : tree = Node( i, x, Empty, Empty) ;;

(* Ogni nodo di un albero, oltre ai figli, ha associato un identificatore (tag) e un’espressione. Quando un albero è definito, le espressioni dei nodi devono essere valutate, e solo quelle. I tag servono a caratterizzare (in maniera eventualmente non univoca) cammini nell’albero. *)


(* AMBIENTI *)

type 't env = ide -> 't;;	(*ambiente polimorfo*)
let emptyenv(v:'t)(x) = v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) (x : ide ) = if x = i then v else applyenv r x;;

(*tipi esprimibili *)
type evT =	Int of int 	| Bool of bool 	| Unbound | Tree of tree | Vuoto
(* Se evFun le diamo scoping statico: si porta appresso l’ambiente *)
| FunVal of evFun 
| RecFunVal of ide * evFun and evFun = ide * exp * evT env 

and tree = Inode of ide * evT * evT * evT
(*  La definizione di evFun mostra che una astrazione funzionale è una chiusura, che comprende: 
nome del parametro formale : ide
codice della funzione dichiarata : exp
ambiente al momento della dichiarazione : evT env *)
	(* Se evFun le diamo scoping dinamico: le togliamo l’ambiente appresso 
| RecFunVal of ide * evFun and evFun = ide * exp	*)
;;


(* TYPE CHECKING *)
let typecheck (s : string) (v : evT) : bool = match s with
	| "int" -> (match v with
		| Int(_) -> true 
|_ -> false) 
| "bool" -> (match v with
		| Bool(_) -> true 
| _ -> false) 
|_ -> failwith("not a valid type");;



(* FUNZIONI PRIMITIVE *)
let prod x y = if (typecheck "int" x) && (typecheck "int" y) then (match (x,y) with 
(Int(n),Int(u)) -> Int(n*u))
else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y) then (match (x,y) with
			(Int(n),Int(u)) -> Int(n+u))
		else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y) then (match (x,y) with
			(Int(n),Int(u)) -> Int(n-u))
		else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y) then (match (x,y) with
			(Int(n),Int(u)) -> Bool(n=u))
		else failwith("Type error");;

let minus x = if (typecheck "int" x)  then (match x with
	   		Int(n) -> Int(-n))
		else failwith("Type error");;

let iszero x = if (typecheck "int" x) then (match x with
			Int(n) -> Bool(n=0))
		else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y) then (match (x,y) with
			 (Bool(b),Bool(e)) -> (Bool(b||e)))
		else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y) then (match (x,y) with
			(Bool(b),Bool(e)) -> Bool(b&&e))
		else failwith("Type error");;

let non x = if (typecheck "bool" x) then (match x with
			| Bool(true) -> Bool(false) 
| Bool(false) -> Bool(true))
else failwith("Type error");;

(* INTERPRETE *)


let rec eval (e : exp) (r : evT env) : evT = match e with
	| Eint n -> Int n 
| Ebool b -> Bool b 
| IsZero a -> iszero (eval a r) 
| Den i -> applyenv r i 
| Eq(a, b) -> eq (eval a r) (eval b r) 
| Prod(a, b) -> prod (eval a r) (eval b r)
| Sum(a, b) -> sum (eval a r) (eval b r) 
| Diff(a, b) -> diff (eval a r) (eval b r) 
| Minus a -> minus (eval a r) 
| And(a, b) -> et (eval a r) (eval b r) 
| Or(a, b) -> vel (eval a r) (eval b r) 
| Not a -> non (eval a r) 
| Ifthenelse(a, b, c) -> let g = (eval a r) in
		if (typecheck "bool" g) then (if g = Bool(true) then (eval b r) else (eval c r))
		else failwith ("nonboolean guard") 
| Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) 
(* L’espressione e2 (ovvero il corpo del blocco) è valutata nell’ambiente “esterno”	esteso	con l’associazione tra	nome i	e valore di e1 *) 

(* Scoping statico *)
| Fun(i, a) -> FunVal(i, a, r) 
| FunCall(f, eArg) -> let fClosure = (eval f r) in (match fClosure with
		| FunVal(arg, fBody, fDecEnv) -> eval fBody (bind fDecEnv arg (eval eArg r)) 
| RecFunVal(f, (arg, fBody, fDecEnv)) -> let aVal = (eval eArg r) in
		let rEnv = (bind fDecEnv f fClosure) in
			let aEnv = (bind rEnv arg aVal) in eval fBody aEnv 
| _ -> failwith("non functional value")) 
     (* 	| FunCall(f, a) -> (match (eval f r) with 
| FunVal(i, b, r1) -> eval b bind(r1, i, (eval a r)) 
| _ -> failwith("non functional value"))
Il corpo della funzione viene valutato nell’ambiente ottenuto legando i parametri formali ai valori dei parametri attuali nell’ambiente r1, nel quale era stata valutata l’astrazione   
      *)

	(*Scoping dinamico 
| Fun(i, a) -> FunVal(i, a) 
| FunCall(f, a) -> (match (eval f r) with 
| FunVal(i, b) -> eval b bind(r, i, (eval a r)) 
| _ -> failwith("non functional value"))
Il corpo della funzione viene valutato nell’ambiente ottenuto legando i parametri formali ai valori dei parametri attuali nell’ambiente r, quello nel quale viene effettuata la chiamata 
*)

| Letrec(f, funDef, letBody) -> (match funDef with
          | Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in eval letBody r1 
          | _ -> failwith("non functional def"))

(* INTERPRETE ETREE *)
|Etree(t) ->( match t with
|Node( a, f, Empty, Empty) ->Tree(Inode(a,(eval f r),Vuoto,Vuoto))
|Node( a, f, Empty, rt) ->
Tree(Inode(a,(eval f r),Vuoto, (eval(Etree(rt))(r))))
|Node( a, f, lt, Empty) ->
Tree(Inode(a,(eval f r),(eval(Etree(lt))(r)),Vuoto))
|Node( a, f, lt, rt) -> 
Tree(Inode(a,(eval f r),(eval(Etree(lt))(r)),(eval(Etree(rt))(r)))) 
|_ ->failwith("Empty tree") )
	
	(* INTERPRETE APPLYOVER *)
| ApplyOver(exf, Etree(t)) -> (match t with
	|Node(a, f, Empty, Empty) -> Tree(Inode(a,(eval exf r),Vuoto,Vuoto))
|Node( a, f, Empty, rt) ->
Tree(Inode(a,(eval exf r),Vuoto, (eval(ApplyOver(exf ,Etree(rt)))(r))))
|Node( a, f, lt, Empty) ->
Tree(Inode(a,(eval exf r),(eval(ApplyOver(exf ,Etree(lt)))(r)),Vuoto))
|Node( a, f, lt, rt) -> 
Tree(Inode(a,(eval exf r),
(eval(ApplyOver(exf ,Etree(lt)))(r)),(eval(ApplyOver(exf ,Etree(rt)))(r)))) 
|_ ->failwith("Empty tree") )	

(* INTERPRETE UPDATE *)
| Update(idl, exf, Etree(t)) -> (match t with
	|Node(a, f, Empty, Empty) -> 
if contains a idl = true then Tree(Inode(a,(eval exf r),Vuoto,Vuoto))
else Tree(Inode(a, (eval f r), Vuoto,Vuoto))
|Node( a, f, Empty, rt) ->
if contains a idl = true 
then Tree(Inode(a,(eval exf r),Vuoto,(eval(Update(idl,exf,Etree(rt)))(r))))
else Tree(Inode(a,(eval f r),Vuoto,(eval(Update(idl,exf,Etree(rt)))(r))))
|Node( a, f, lt, Empty) ->
	if contains a idl = true 
then Tree(Inode(a,(eval exf r),(eval(Update(idl,exf,Etree(lt)))(r)),Vuoto))
else Tree(Inode(a,(eval f r),(eval(Update(idl,exf,Etree(lt)))(r)),Vuoto))
|Node( a, f, lt, rt) -> 
	if contains a idl = true 
then Tree(Inode(a,(eval exf r),
(eval(Update(idl,exf,Etree(lt)))(r)),(eval(Update(idl,exf,Etree(rt)))(r))))
else Tree(Inode(a,(eval f r),
(eval(Update(idl,exf,Etree(lt)))(r)),(eval(Update(idl,exf,Etree(rt)))(r))))
|_ ->failwith("Empty tree") )	

	(* INTERPRETE SELECT *)
| Select(idl,exf, Etree (t)) -> let g = (eval exf r) in
		if (typecheck "bool" g) then (if g = Bool(false) then Unbound 
else (match t with  
	|Node(a, f, Empty, Empty) -> 
if (contains a idl = true) then Tree(Inode(a,(eval f r),Vuoto,Vuoto))
else Unbound 
|Node( a, f, Empty, rt) ->
if (contains a idl = true) 
then Tree(Inode(a,(eval f r),Vuoto,(eval(Etree(rt))(r)))) 	
(*else Tree(Inode(a,(eval f r),Vuoto,(eval(Select(idl,exf,Etree(rt)))(r))))*)
else (eval(Select(idl,exf,Etree(rt)))(r))
|Node( a, f, lt, Empty) ->
	if (contains a idl = true)
then Tree(Inode(a,(eval f r),(eval(Etree(lt))(r)),Vuoto))
(*else Tree(Inode(a,(eval f r),(eval(Select(idl,exf,Etree(lt)))(r)),Vuoto))*)
else (eval(Select(idl,exf,Etree(lt)))(r))
|Node( a, f, lt, rt) -> 
	if (contains a idl = true) 
then Tree(Inode(a,(eval f r),(eval(Etree(lt))(r)),(eval(Etree(rt))(r))))
(* else Tree(Inode(a,(eval f r),
(eval(Select(idl,exf,Etree(lt)))(r)),(eval(Select(idl,exf,Etree(rt)))(r)))) *)
else let v1=(eval(Select(idl,exf,Etree(lt)))(r)) in 
	if v1 = Unbound then let v2 = (eval(Select(idl,exf,Etree(rt)))(r))
		in if v2 = Unbound then Unbound 
			else v2 
	else v1	
| _ -> failwith("Empty tree") ))
else failwith ("nonboolean guard") 

and contains i l = match l with
	| [] -> false
        	| [x] -> if x = i then true else false 
	| h :: t -> if h = i then true else (contains i t)
;;


(* ESEMPI PRIMITIVI 
eval (Eint (2))(emptyenv Unbound);;
eval (Ebool (true))(emptyenv Unbound);;
eval (Ebool (false))(emptyenv Unbound);;
eval (IsZero (Eint 2))(emptyenv Unbound);;
eval (Den ("ciao"))(emptyenv Unbound);;
eval (Eq ((Eint 2),(Eint 2)))(emptyenv Unbound);;
eval (Eq ((Eint 2),(Eint 3)))(emptyenv Unbound);;
eval (Prod ((Eint 2),(Eint 3)))(emptyenv Unbound);;
eval (Sum ((Eint 2),(Eint 3)))(emptyenv Unbound);;
eval (Diff ((Eint 5),(Eint 3)))(emptyenv Unbound);;
eval (Minus (Eint (-3)))(emptyenv Unbound);;
eval (Minus (Eint (3)))(emptyenv Unbound);;
eval (And ((Ebool true),(Ebool true)))(emptyenv Unbound);;
eval (And ((Ebool true),(Ebool false)))(emptyenv Unbound);;
eval (Or ((Ebool true),(Ebool false)))(emptyenv Unbound);;
eval (Or ((Ebool false),(Ebool false)))(emptyenv Unbound);;
eval (Not (Ebool false))(emptyenv Unbound);;
eval (Not (Ebool true))(emptyenv Unbound);;
eval (Ifthenelse ((Ebool true),(Eint 1),(Eint 0)))(emptyenv Unbound);; 
eval (Ifthenelse ((Ebool false),(Eint 1),(Eint 0)))(emptyenv Unbound);;
(* Valutazione -: evT = Int 3*)
eval (Let(
"x", 
Sum(Eint 1, Eint 0), 
Let(
"y", 
Ifthenelse(Eq(Den "x", Eint 0), Diff(Den "x", Eint 1), Sum(Den "x", Eint 1)), 
Let("z", Sum(Den "x", Den "y"), Den "z")
)
) ) (emptyenv Unbound);;
(* Sintassi -: int = 3*)
 let x = 1+0 in let y = if x = 0 then x-1 else x+1 in let z = x+y in z;;  

(* Valutazione -: evT = Int 6*)
eval (Letrec(
	"fact",
	Fun(
		"n",
Ifthenelse(
	Eq(Den "n", Eint 0),
	Eint 1,
	Prod(Den "n", FunCall(Den "fact", Diff(Den "n", Eint 1)))
)
),
FunCall(Den "fact", Eint 3)
))(emptyenv Unbound) ;;

(* Sintassi -: int = 6*)
let rec fact = fun n -> if n = 0 then 1 else n * fact (n-1) in fact(3);;
*)

(* ESEMPI ETREE *)
(* Per non ripetere Empty Empty usiamo la funzione ausiliaria leaf )
eval (Etree(Node("a",Eint 3, Empty, Empty)))(emptyenv Unbound);; 
eval (Etree(leaf "a" (Eint 3)))(emptyenv Unbound);;

eval (Etree(Node("a",Prod ((Eint 2),(Eint 3)), Empty, Empty)))(emptyenv Unbound);; 
eval (Etree(leaf "a" (Prod ((Eint 2),(Eint 3)))))(emptyenv Unbound);;

eval (Etree(Node("a",Eint 2, 
Empty, 
Node("b", Diff ((Eint 3),(Eint 2)), Empty,Empty)
)))(emptyenv Unbound);; 
eval (Etree(Node("a",Eint 2, 
Empty, 
(leaf "b" (Diff ((Eint 3),(Eint 2))) )
)))(emptyenv Unbound);; 

eval (Etree(Node("a",Eint 2, 
Node("b",Sum ((Eint 3),(Eint 2)), Empty,Empty),
Empty)))(emptyenv Unbound);; 
eval (Etree(Node("a",Eint 2, 
(leaf "b" (Sum ((Eint 3),(Eint 2))) ), 
Empty)))(emptyenv Unbound);; 

eval (Etree(Node("a",Eint 2, 
Node("b",Eq((Eint 3),(Eint 2)),Empty,Empty),
Node("c",Eq((Eint 3),(Eint 3)),Empty,Empty)
)))(emptyenv Unbound);; 
eval (Etree(Node("a",Eint 2, 
( leaf "b" ( Eq((Eint 3),(Eint 2)) ) ), 
( leaf "c" ( Eq((Eint 3),(Eint 3)) ) )
)))(emptyenv Unbound);; 

eval (Etree(Node( "a", Eint 3, 
Node( "b", Eint 2, Empty, leaf  "c" (Eint 1)), 
Node( "d", Eint 2, leaf "e" (Eint 3), leaf "f" (Eint 1)))))(emptyenv Unbound);;

(* ESEMPI APPLYOVER*)
eval (ApplyOver( Eint 2, Etree(Node( "a", Eint 3, Empty, Empty))))(emptyenv Unbound);;
eval (ApplyOver( Eint 2, Etree(leaf "a"  (Eint 3))))(emptyenv Unbound);;
eval (ApplyOver( Sum((Eint 2),(Eint 3)), Etree(leaf "a"  (Eint 3))))(emptyenv Unbound);;

eval (ApplyOver( Sum((Eint 2),(Eint 3)), 
Etree("a", Eint 2, 
Empty, 
Node( "b", Eint 3, Empty, Empty))))(emptyenv Unbound);;

eval (ApplyOver( Sum((Eint 2),(Eint 3)), Etree(Node( "a", Eint 1, 
Node( "b", Eint 2, Empty, Node( "c", Eint 3, Empty, Empty)), 
Node( "d", Eint 4, Empty, Node( "e", Eint 6, Empty, Empty))) )))
(emptyenv Unbound);;

(* ESEMPI UPDATE *)
eval (Update(["a"], Eint 2, Etree(Node( "a", Eint 3, Empty, Empty))))(emptyenv Unbound);;
eval (Update(["b"], Eint 2, Etree(Node( "a", Eint 3, Empty, Empty))))(emptyenv Unbound);;

eval (Update(["a"], Sum((Eint 2),(Eint 3)), 
Etree(Node( "a", Eint 3, Empty, Empty))))(emptyenv Unbound);;

eval (Update(["a"; "c";"e"], Sum((Eint 2),(Eint 3)), Etree(Node( "a", Eint 1, 
Node( "b", Eint 2, Empty, Node( "c", Eint 3, Empty, Empty)), 
Node( "d", Eint 4, Empty, Node( "e", Eint 6, Empty, Empty))) )))
(emptyenv Unbound);;

(* ESEMPI SELECT *)
eval (Select(["a"], Ebool true, Etree(Node( "a", Eint 3, Empty, Empty))))
(emptyenv Unbound);;

eval (Select(["b"], Ebool true, Etree(Node( "a", Eint 3, Empty, Empty))))
(emptyenv Unbound);;

eval (Select(["a"], Ebool false, Etree(Node( "a", Eint 3, Empty, Empty))))
(emptyenv Unbound);;

eval (Select(["a"; "c";"e"], Ebool true , Etree(Node( "b", Eint 1, 
Empty,
Node( "a", Eint 2, Empty, Empty) )) ) )
(emptyenv Unbound);;

eval (Select(["a"; "c";"e"], Ebool true , Etree(Node( "b", Eint 1,
Node( "a", Eint 2, Empty, Empty), 
Empty)) ) )
(emptyenv Unbound);;


eval (Select([ "e";"b"], Ebool true , Etree(Node( "a", Eint 1, 
Node( "b", Eint 2, Empty, Node( "c", Eint 3, Empty, Empty)), 
Node( "d", Eint 4, Empty, Node( "e", Eint 6, Empty, Empty))) )))
(emptyenv Unbound);;


(* FUNZIONI DI STAMPA DELL’ALBERO *)

(* una rappresentazione della figura dell’albero *)
type picture = string array ;;

(* una figura ha alcune informazioni extra tra le quali 
    rootx che è la coordinata x, che inizia da 0, ovvero dalla radice principale dell’albero *)
type tree_block = {	width : int;	height : int;	rootx : int;	picture : picture; } ;;

let char_of_int (i:int) : char = Char.chr ((Char.code '0') + i) ;;

(* crea un nuovo tree_block con un valore radice v immesso a rx *)
let new_tb (w:int) (h:int) (rx:int) (v:int) =
  let pic = Array.init h (fun _ -> String.make w ' ') in
  let _ = Bytes.set (pic.(0)) rx  (char_of_int v) in
{ width = w;	height = h;	rootx = rx;	picture = pic;} ;;

(* inserisce nuove linee nel tree_block per renderle una singola stringa *)
let string_of_tree_block (b:tree_block) : string = String.concat "\n" (Array.to_list (b.picture)) ;;

(* eccezione lanciata se c’è una sovrapposizione rilevata quando si prova a sovraimpostare 2 alberi *)
exception Overlap ;;

(* copia un tree_block in un altro, non controllando se c’è sovrapposizione 
   x = posizione di partenza 
   dy = ammontare di posizioni da shiftare il blocco copiato verticalmente
*)
let overwrite (dst:tree_block) (src:tree_block) (x:int) (dy:int) : unit =
  for i = 0 to src.height - 1 do
    String.blit (src.picture.(i)) x (dst.picture.(i+dy)) x src.width
  done
;;

(* copia un tree_block in un altro, controllando se ci sono collisioni (ovvero sovrapposizioni)   dx e dy sono gli offsets per spostare il blocco generatore relativo al target *)
let try_to_write (dst:tree_block) (src:tree_block) (dx:int) (dy:int) : unit =
  for i = 0 to src.height - 1 do
    for j = 0 to src.width - 1 do
      let y = i+dy in
      let x = j+dx in
      let src_char = String.get (src.picture.(i)) j in
	if((String.get (dst.picture.(y)) x) <> ' ') && (src_char <> ' ') then raise Overlap
	else Bytes.set (dst.picture.(y)) x src_char
    done
  done
;;

(* disegna un bordo obliquo sinistro di lunghezza el iniziando dalla radice rx *)
let draw_left_edge (dst:tree_block) (el:int) (rx:int) : unit =
  for i = 1 to el do
    Bytes.set dst.picture.(i) (rx - i) '/'
  done
;;

(* disegna un bordo obliquo destro di lunghezza el iniziando dalla radice rx *)
let draw_right_edge (dst:tree_block) (el:int) (rx:int) : unit =
  for i = 1 to el do
    Bytes.set dst.picture.(i) (rx + i) '\\'
  done
;;

(* sovraimpone 2 tree_blocks e dà a loro una nuova radice r, essa prova a connettere i 2 alberi alla radice usando un bordo di lunghezza el.
Lancia 'Overlap' se c’è una collisione in questo processo *)
let superimpose (b1:tree_block) (b2:tree_block) (r:int) (el:int) : tree_block =
  let dx = el * 2 + 2 in
  let dy = el + 1 in 
  let new_height = dy + (max b1.height b2.height) in
  let (fixed_block, shifted_block, shift_amt, new_width, new_rootx) = 
    if (b1.rootx + dx) >= b2.rootx then (* b1 is not shifted *)
      let amt = b1.rootx + dx - b2.rootx in
      let w = max b1.width (b1.rootx + dx +(b2.width - b2.rootx)) in
      let rx = b1.rootx + dy in
	(b1, b2, amt, w, rx)
    else (* b1 is shifted *)
      let amt = b2.rootx - (b1.rootx + dx) in
      let w = max (b1.width + amt) b2.width in
      let rx = b1.rootx + amt + dy in
	(b2, b1, amt, w, rx)
  in
  let new_block = new_tb new_width new_height new_rootx r in
  let _ = overwrite new_block fixed_block 0 dy in
  let _ = try_to_write new_block shifted_block shift_amt dy in
  let _ = draw_left_edge new_block el new_rootx in
  let _ = draw_right_edge new_block el new_rootx in
    new_block
;;

(* Fonde 2 tree_blocks provando a connetterli in una nuova radice.
Inizia con il bordo di lunghezza più piccola possibile e lo incrementa fino a che non si rilevano sovrapposizioni di collisioni *)
let merge (b1:tree_block) (b2:tree_block) (r:int) : tree_block =
  let rec loop (el:int) : tree_block = try superimpose b1 b2 r el with
      | Overlap -> loop (el+1)
  in
    loop 1
;;

(* crea un tree_block nel figlio sinistro di una nuova radice r *)
let make_left_child (t:tree_block) (r:int) : tree_block =
  let new_height = t.height + 2 in
  let new_width = max (t.width) (t.rootx + 3) in
  let new_rootx = t.rootx + 2 in
  let new_block = new_tb new_width new_height new_rootx r in
  let _ = overwrite new_block t 0 2 in
  let _ = draw_left_edge new_block 1 new_rootx in
    new_block
;;

(* crea un tree_block nel figlio destro di una nuova radice r *)
let make_right_child (t:tree_block) (r:int) : tree_block =
  let new_height = t.height + 2 in
  let shift_amt = max 0 (2 - t.rootx) in
  let new_width = t.width + shift_amt in
  let new_rootx = max 0 (t.rootx - 2) in
  let new_block = new_tb new_width new_height new_rootx r in
  let _ = try_to_write new_block t shift_amt 2 in
  let _ = draw_right_edge new_block 1 new_rootx in
    new_block
;;

(* crea un tree_block vuoto *)
let empty_block () : tree_block =  {height=0; width=0; rootx=0; picture=Array.make 0 ""} ;;

(* crea un tree_block con soltanto un nodo, il quale è sia radice sia foglia *)
let leaf_block (r:int) : tree_block =
  {  height=1;  width=1;  rootx=0;  picture=Array.make 1 (String.make 1 (char_of_int r));} ;;

let expToInt (e:exp) : int = match e with
 | Eint n -> n ;;

(* ricorsivamente costruisce un tree_block dall’albero usando 'merge' per trovare una figura ottimale non-sovraimposta per i figli *)
let rec block_of_tree (t:tree) : tree_block = match t with
    | Empty -> empty_block ()
    | Node( a , r, Empty, Empty) -> (leaf_block(expToInt r) )
    | Node( a , r, Empty, rt) -> let rtb = block_of_tree rt in (make_right_child rtb (expToInt r) )
    | Node( a, r, lt, Empty) -> let ltb = block_of_tree lt in (make_left_child ltb ( expToInt r) )
    | Node( a, r, lt, rt) ->
	let ltb = block_of_tree lt in
	let rtb = block_of_tree rt in
	 (merge ltb rtb ( expToInt r) )
;;

(* The main function: assumes that the nodes are in [0-9] *)
let string_of_tree (t:tree) : string =  string_of_tree_block (block_of_tree t) ;;

let top_print (ppf:Format.formatter) (t:tree) : unit =Format.fprintf ppf "\n%s" (string_of_tree t);;


(*TRASFORMAZIONE DA ALBERO A LISTA*)

let rec treeToList (t:tree) = match t with
| Empty -> []
| Node( a , r, Empty, Empty) -> [(a , (expToInt r))]
| Node( a , r, Empty, rt) -> [(a , (expToInt r))] @ treeToList rt
| Node( a, r, lt, Empty) -> [(a , (expToInt r))] @ treeToList lt
| Node( a, r, lt, rt) -> [(a , (expToInt r))] @ treeToList lt @ treeToList rt 
;;

(* ESEMPI DI ALBERI GRAFICI*)

Etree(Node( "a", Eint 3, 
Node( "b", Eint 2, Empty, leaf  "c" (Eint 1)), 
Node( "d", Eint 2, leaf "e" (Eint 3), leaf "f" (Eint 1))) );;
let t1 =  Node( "a", Eint 3, 
Node( "b", Eint 2, Empty, leaf  "c" (Eint 1)), 
Node( "d", Eint 2, leaf "e" (Eint 3), leaf "f" (Eint 1))) ;;
print_endline "- - - t1 - - -"; print_endline (string_of_tree t1) ;;
treeToList t1;;

let t2 = Node("a", Eint 1, 
Node("b", Eint 2, Empty, Empty),	
Node("c", Eint 3, Empty, Empty)) ;;
print_endline "- - - t2 - - -"; print_endline (string_of_tree t2) ;;
treeToList t2;;

let t3 = 
Node("a",Eint 7, 
Empty,
Node("b", Eint 6, 
Node("c", Eint 5, Node("d", Eint 4, Node("e", Eint 3, Empty, Empty), Empty),Empty),Empty));;
print_endline "- - - t3 - - -"; print_endline (string_of_tree t3);;
treeToList t3;;

let t5 =  
Node("a", Eint 0, 
Node("b", Eint 1, leaf "c" (Eint 2), Empty),
Node("d", Eint 6, leaf "e" (Eint 7), leaf "f" (Eint 8))) ;; 
print_endline "- - - t5 - - -" ; print_endline (string_of_tree t5) ;; 
treeToList t5;; 

