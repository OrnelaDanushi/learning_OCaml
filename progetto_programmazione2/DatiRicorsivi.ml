tree

(* definizione *)
type tree =
| Leaf of int 
| Node of tree * int * tree ;;

type tree =
	| Empty
| Node of tree * int * tree ;;

type 'a tree =
	| Empty
| Node of 'a tree * 'a * 'a tree ;;


(* applicazione
	ricerca in un albero 
	val contains : tree -> int -> bool = <fun>
 *)
let rec contains (t:tree) (n:int) :bool = match t with
   	| Empty -> false
   	| Node ( lt, x, rt ) -> x=n || (contains lt n) || (contains rt n);;

binaryTree
(* definizione *)
type binaryTree = 
| Empty 
| Node of binaryTree * int * binaryTree;;


(* applicazione
	ricerca in un albero binario
IR: Node( lf, x, rt) è un ABR sse 
			lt e rt sono ABR
			ogni nodo lt < x
			ogni nodo rt > x
	val contains : binaryTree -> int -> bool = <fun>
 *)
let rec containsBinary (t:binaryTree) (n:int) :bool = match t with
| Empty -> false
  	| Node ( lt, x, rt ) -> if x=n then true 
       else 
                         		if n<x then (containsBinary lt n) 
                               		else (containsBinary rt n);;               

(* 	inserimento	*)
let rec insertBinary (t:binaryTree)(n:int) :binaryTree = match t with
   | Empty -> Node(Empty, n, Empty)
   | Node (lt, x, rt) -> if x = n then t
                        else
                           if n<x then Node((insertBinary (lt)(n)), x, rt)
                           else Node(lt, x, (insertBinary (rt)(n)));;

(* ricerca del max *)
let rec maxBinary (t:binaryTree) :int = match t with
  |Node( _, x, Empty) -> x
   |Node( _, _, rt) -> maxBinary rt 
   |_ -> failwith "maxBinary called on Empty binaryTree";;


(* rimozione di un elemento *)
let rec deleteBinary (t:binaryTree)(n:int) :binaryTree = match t with
   | Empty -> Empty
   | Node(lt, x, rt) -> if x=n then match (lt, rt) with
                           |(Empty, Empty) -> Empty
                           |(Node _, Empty) -> lt
                           |(Empty, Node _) -> rt
                           | _ -> let m = maxBinary lt in
                                 Node(deleteBinary lt m, m, rt)
                        else
                           if x<n then Node(deleteBinary lt n, x, rt)
                           else Node(lt, x, deleteBinary rt n);;     

