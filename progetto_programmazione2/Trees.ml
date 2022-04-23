(* TREES *)

(* A type of integer-carrying trees *)
type tree = Empty | Node of tree * int * tree ;;

(* helper function for constructing trees *)
let leaf (i:int) : tree = Node(Empty, i, Empty) ;;

(* determines whether a node is a leaf *)
let is_leaf (t:tree) : bool = match t with
    | Node(Empty,_,Empty) -> true
    | _ -> false ;;

(* tree pretty printer *)

(* a representation of pictures *)
type picture = string array ;;

(* a picture with some extra information:
    rootx is the x coordinate (starting from 0) of the root character of this tree 
*)
type tree_block = {	width : int;	height : int;	rootx : int;	picture : picture; } ;;

let char_of_int (i:int) : char = Char.chr ((Char.code '0') + i) ;;

(* creates a new tree block with a root value v rooted at rx *)
let new_tb (w:int) (h:int) (rx:int) (v:int) =
  let pic = Array.init h (fun _ -> String.make w ' ') in
  let _ = Bytes.set (pic.(0)) rx  (char_of_int v) in
{ width = w;	height = h;	rootx = rx;	picture = pic;} ;;

(* inserts newlines into a treeblock to serialize it as a single string *)
let string_of_tree_block (b:tree_block) : string = String.concat "\n" (Array.to_list (b.picture)) ;;

(*an exception raised if there is overlap detected when trying to superimpose two trees *)
exception Overlap ;;

(* copies one tree_block into another; doesn't check for overlap 
   x = starting x position
   dy = amount to shift the copied block vertically
*)
let overwrite (dst:tree_block) (src:tree_block) (x:int) (dy:int) : unit =
  for i = 0 to src.height - 1 do
    String.blit (src.picture.(i)) x (dst.picture.(i+dy)) x src.width
  done
;;

(* copies on tree_block into another, checking for collisions (overlap)
   dx and dy are offsets to shift the source block relative to the target *)
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

(* draws an left-slanting edge of length el starting at root rx *)
let draw_left_edge (dst:tree_block) (el:int) (rx:int) : unit =
  for i = 1 to el do
    Bytes.set dst.picture.(i) (rx - i) '/'
  done
;;

(* draws a right-slanting edge of length el starting at root rx *)
let draw_right_edge (dst:tree_block) (el:int) (rx:int) : unit =
  for i = 1 to el do
    Bytes.set dst.picture.(i) (rx + i) '\\'
  done
;;

(* superimposes two tree_blocks and gives them a new root r.
   it tries to connect the two trees to the root using an edge of length el. 
   Raises 'Overlap' if there is a collision in this process *)
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

(* merges two tree blocks by trying to connect them to a new root.  
    It starts with the smallest possible edge length and increases it until no collision overlaps are detected *)
let merge (b1:tree_block) (b2:tree_block) (r:int) : tree_block =
  let rec loop (el:int) : tree_block = try superimpose b1 b2 r el with
      | Overlap -> loop (el+1)
  in
    loop 1
;;

(* makes a tree_block into the left child of a new root r *)
let make_left_child (t:tree_block) (r:int) : tree_block =
  let new_height = t.height + 2 in
  let new_width = max (t.width) (t.rootx + 3) in
  let new_rootx = t.rootx + 2 in
  let new_block = new_tb new_width new_height new_rootx r in
  let _ = overwrite new_block t 0 2 in
  let _ = draw_left_edge new_block 1 new_rootx in
    new_block
;;

(* makes a tree_block into the right child of a new root r *)
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

(* creates an empty tree_block *)
let empty_block () : tree_block =  {height=0; width=0; rootx=0; picture=Array.make 0 ""} ;;

(* creates a tree_block with just one node, which is both the root and leaf *)
let leaf_block (r:int) : tree_block =
  {  height=1;  width=1;  rootx=0;  picture=Array.make 1 (String.make 1 (char_of_int r));} ;;

(* recursively constructs a tree_block from a tree using 'merge' to find an optimal non-overlapping picture for the children *)
let rec block_of_tree (t:tree) : tree_block = match t with 
    | Empty -> empty_block ()
    | Node(Empty, r, Empty) -> leaf_block r
    | Node(Empty, r, rt) -> let rtb = block_of_tree rt in make_right_child rtb r
    | Node(lt, r, Empty) -> let ltb = block_of_tree lt in make_left_child ltb r
    | Node(lt, r, rt) ->
	let ltb = block_of_tree lt in
	let rtb = block_of_tree rt in
	  merge ltb rtb r
;;

(* The main function: assumes that the nodes are in [0-9] *)
let string_of_tree (t:tree) : string =  string_of_tree_block (block_of_tree t) ;;

let top_print (ppf:Format.formatter) (t:tree) : unit =Format.fprintf ppf "\n%s" (string_of_tree t);;


(* ASSERT *)
open Printf ;;
open List ;;

(* When set to true, stop immediately on a failing test *)
let stop_on_failure_flag = ref false ;;

let stop_on_failure () = stop_on_failure_flag := true ;;

let error_mesg (s: string) =  print_endline s; if !stop_on_failure_flag then exit 1 else () ;;

type result = Succ | Fail | Err of string ;;

let assert_eqf (msg: string) actual_fcn expected : unit =
  let _ = print_string ("Running: "^msg^" ... ") in 
  let _ = flush_all () in
  let outcome = try if expected = (actual_fcn ()) then Succ else Fail with 
       | Failure s -> Err s
                   | e         -> Err (Printexc.to_string e) in
 
  match outcome with 
             | Succ -> print_endline ("Test passed!")
             | Fail -> print_newline (); error_mesg ("Test failed: "^msg^"\n")
             | Err s -> print_newline (); error_mesg ("Test error: `"^msg^"` reported `" ^ s ^ "`\n")
     ;;

let assert_eq (msg:string) actual expected : unit = assert_eqf msg (fun ()->actual) expected ;;
 
let run_test msg f = assert_eqf msg f true ;;

let run_failing_test msg f = 
  let _ = print_string ("Running: "^msg^" ... ") in
  let _ = flush_all () in
  let result = (try (ignore (f ()) ; Fail) with  | _ -> Succ) in match result with 
  	| Succ -> print_endline ("Test passed!")
  	| Fail -> error_mesg ("Test error: should have failed.") 
  	| Err s -> error_mesg ("run_failing_test BUG: shouldn't get here.")
;;	
	
stop_on_failure() ;;


(* SOME EXAMPLE TREES *)
let t1 =  Node(Node(Empty,2,leaf 1),3,Node(leaf 3,2,leaf 1)) ;;
print_endline "--- t1 ---" ; print_endline (string_of_tree t1) ;; 

let t3=Node(Empty,7,Node(Node(Node(Node(Empty,3,Empty),4,Empty),5,Empty),6,Empty));;
print_endline "--- t3 ---"; print_endline (string_of_tree t3);; 

let t5 =  Node(Node(leaf 2, 1, Empty),0, Node(leaf 7, 6, leaf 8)) ;; 
print_endline "--- t5 ---" ; print_endline (string_of_tree t5) ;; 

(* SUMS ALL OF THE INTEGERS APPEARING IN A TREE *)
let rec sum (t:tree) : int = match t with
	| Empty -> 0
  	| Node (lt, v, rt) -> v + sum lt + sum rt
;;
	
let test () : bool = sum t1 = 12 ;; 
run_test "sum t1" test ;; 

let test () : bool = sum Empty = 0 ;;
run_test "sum Empty" test ;;

let test () : bool = sum (Node(Empty,2,Empty)) = 2 ;; 
run_test "sum (leaf 2)" test ;;

(* COUNTS THE LONGEST PATH FROM THE ROOT TO A LEAF NODE *)
let rec height (t:tree) : int = match t with
	| Empty -> 0
	| Node (lt, _, rt) -> 1 + max (height lt) (height rt)
;;	
	
let test () : bool = height t1 = 3 ;;
run_test "height t1" test ;;

let test () : bool = height Empty = 0 ;;	
run_test "height Empty" test ;;

let test () : bool = height (Node(Empty,2,Empty)) = 1 ;; 
run_test "height leaf" test ;;

(* RETURNS THE IN-ORDER TRAVERSAL OF THE TREE *)
let rec inorder (t:tree) : int list = match t with
	| Empty -> []
	| Node (lt, x, rt) ->
		let l1 = inorder lt in
		let l2 = inorder rt in
		l1 @ (x :: l2) 
;;

let test () : bool = inorder t1 = [2;1;3;3;2;1] ;; 
run_test "inorder t1" test ;;

let test () : bool = inorder Empty = [] ;; 
run_test "inorder Empty" test ;;

let test () : bool = inorder (Node(Empty,2,Empty)) = [2] ;; 
run_test "inorder leaf" test ;;

(* RETURNS THE PRE-ORDER TRAVERSAL OF THE TREE *)
let rec preorder (t:tree) : int list = failwith "preorder" ;;

(* RETURNS THE POST-ORDER TRAVERSAL OF THE TREE *)
let rec postorder (t:tree) : int list = match t with
    | Empty -> []
    | Node(l,n,r) -> failwith "postorder"
;;

(* A PRE-ORDER SEARCH THROUGH AN ARBITRARY TREE

  returns true if the tree contains n *)
let rec contains (t:tree) (n:int) : bool = match t with
	| Empty -> false
	| Node (lt, x, rt) -> n = x || contains lt n || contains rt n
;;
	
let test () : bool = contains Empty 3 = false ;; 
run_test "contains Empty" test ;;

let test () : bool = contains (Node(Empty,2,Empty)) 2=true ;; 
run_test "contains leaf 2" test ;;

let test () : bool = contains (Node(Empty,2,Empty)) 3=false ;; 
run_test "contains leaf 2" test ;;

let test () : bool = contains t1 1 = true ;; 
run_test "contains t1 1" test ;;

