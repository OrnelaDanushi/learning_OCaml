
type ide = string ;;

(* un valore di tipo record e' un dato strutturato composto da
un numero finito di coppie nome-valore, detti campi

analogamente, una espressione di tipo record e' composta da 
un numero finio di coppie nome-valore.
La valutazione di una espressione record produce un valore record.

un identificatore puo' esser legato ad un valore record tramite il costrutto let
es: espressione record che compare nel let e' valutata in un valore record
let rect = record{base = 5*5, altezza = 10-6}
val rect = record{base = 25, altezza = 4}

sui record e' definita l'operazione di selezione di una componente
let b = rect.base
val b = 25
*)

type exp = 
  | Int of int
  | Den of ide
  | Let of ide * exp * exp
  | Record of (ide * exp) list
  | Select of exp * ide ;;

type dexp = 
  | DInt of int
  | DRec of (ide * dexp) list;;

exception EmptyEnv;;

let env0 = fun x -> raise EmptyEnv;;                            (* Ambiente locale default *)

let ext env (x: ide) v = fun y -> if x=y then v else env y;;    (* Estensione di ambiente *)

(*
env : string -> 'a
ext : (string -> 'a) * string * 'a -> string -> 'a
*)

(* valutazione di espressioni NB: booleani rappresentati da 0 e 1 *)
let rec eval e env = match e with
 | Int i -> DInt i
 | Den x -> env x
 | Let (x, e1, e2) -> let v = (eval e1 env) in
   let env1 = (ext env x v) in
     (eval e2 env1)
 | Record e1 -> let v = (evalList e1 env) in DRec v
 | Select (e1, i) -> match e1 with
   Den x -> (match env x with
   DRec c -> (lookup i c)
   | _ -> failwith "wrong ide in select")
   | _ -> failwith "wrong exp in select"
  and evalList el env = match el with
   [] -> []
   | (i,e)::el1 -> (i, (eval e env)):: (evalList el1 env)
  and lookup x c = match c with 
   [] -> failwith "wrong field in select"
   | (y, v)::c1 -> if x = y then v else lookup x c1 ;;

let dIntToInt de = match de with 
   | DInt x -> x
   | _ -> failwith "wrong int" ;; 

print_int (dIntToInt (eval (Let("x",Record([("z", Int 7);("y",Int 5)]),Select(Den "x","y"))) env0)) ;;


