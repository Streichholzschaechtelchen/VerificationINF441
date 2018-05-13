module Fraction =
  struct
    type frac = |Frac of int * int |Infty

    let foi n = Frac (n, 1)

    let rec pgcd a b = match b with
      |0 -> a
      |b -> pgcd b (a mod b)

    let norm x = match x with
      |Frac(a, b) -> let d = pgcd a b in if b > 0 then Frac(a / d, b / d) else Frac(-a / d, b / d)
      |_ -> Infty

    let sum x y = match (x, y) with
      |Frac (a, b), Frac(c, d) -> norm (Frac(a * d + c * b, b * d))
      |_-> Infty

    let sub x y = match (x, y) with
      |Frac (a, b), Frac(c, d) -> norm (Frac(a * d - c * b, b * d))
      |_-> Infty

    let opp x = match x with
      |Frac(a, b) -> norm (Frac(-a, b))
      |_-> Infty

    let prod x y = match (x, y) with
      |Frac (a, b), Frac(c, d) -> norm (Frac(a * c, b * d))
      |_ -> Infty

    let inv x = match x with
      |Frac(0, _) -> Infty
      |Frac(a, b) -> norm (Frac(b, a))
      |_ -> Infty
	      
    let div x y = prod x (inv y)

    let pos x = match x with
      |Frac(a, b) -> a * b >= 0
      | _ -> true

    let geq x y = match x, y with
      |Infty, _               -> true
      |Frac(a, b), Frac(c, d) -> a * d >= b * c
      |_ , _                  -> false

    let eq x y = match x, y with
      |Infty, Infty           -> true
      |Infty, _ |_, Infty     -> false
      |Frac(a, b), Frac(c, d) -> a * d = b * c   

    let print_frac x = match x with
      |Frac(a, b) -> print_int a ; print_string " / " ; print_int b
      |Infty -> print_string "Infty"
  end

open Fraction

let print_array a =
  let n = Array.length a in
  for i = 0 to n - 1 do
    print_frac a.(i); print_string " ; "
  done;
  print_string "\n"
		      
let print_matrix a = let n = Array.length a in let m = Array.length a.(0) in
  for i = 0 to n - 1 do
    for j = 0 to m - 1 do
      print_frac a.(i).(j) ; print_string " ; "
    done;
    print_string "\n"
  done

let pivot a n m i j =
  print_string "pivot with n = " ; print_int n ; print_string ", m = " ; print_int m ; print_string ", i = " ; print_int i ; print_string ", j = " ; print_int j ; print_string "\n";
  let x = a.(i).(j) in
  print_string "Found x = " ; print_frac x ; print_string "\n" ;
  for l = 0 to m - 1 do
    a.(i).(l) <- prod a.(i).(l) (inv x)
  done;
  print_string "Done the line i = " ; print_int i ; print_string "\n";
  for k = 0 to n - 1 do
    if not (k = i) then
    (let y = a.(k).(j) in
    for l = 0 to m - 1 do
     a.(k).(l) <- sum a.(k).(l) (opp (prod y a.(i).(l)))
    done)
  done;
  print_string "After the pivot the matrix is : \n" ; print_matrix a ; print_string "\n"

let find_pivot a n m k l =
  let j = ref 0 in
  while !j < l && pos (opp a.(0).(!j)) do j := !j + 1 done;
  if !j = l then None else
  (print_string "I found a strictly positive column and it is "; print_int !j; print_string "\n";
  let i = ref 1 in
  let lig = ref None in
  while !i < k do
    if not (pos (opp a.(!i).(!j))) then (print_string "I found a positive one \n" ; match !lig with
      |None -> lig := Some !i
      |Some i0 -> let c = pos (sum (prod (inv a.(i0).(!j)) a.(i0).(m - 1)) (opp (prod (inv a.(!i).(!j)) a.(!i).(m - 1))))
        in if c then lig := Some !i
    );
    i := !i + 1;
    (* raise (Failure "begin"); *)
  done;
  print_string "I chose line " ; print_int (!i - 1); print_string "\n";
  Some(Some !j, !lig))

let simplex a b k l =
  print_string "Enter simplex \n";
  let pivot_array = Array.make (k + 1) [||] in
  for i = 0 to k do
    let idlig = Array.make k (foi 0) in
    if i > 0 then idlig.(i - 1) <- (foi 1);
    pivot_array.(i) <- Array.concat [idlig ; a.(i) ; [|b.(i)|]]
  done;
  print_string "Aux array created and is \n" ; print_matrix pivot_array ;
  let rec simplex_rec pivot_array k l =
    print_string "Enter recursion\n";
    let piv = find_pivot pivot_array (k + 1) (k + l + 2) (k + 1) (k + l + 1) in match piv with
      |None -> print_string "case 1\n" ; pivot_array.(0).(k + l + 1)
      |Some (_, None) -> print_string "case 2\n" ; Infty
      |Some (Some j, Some i) -> print_string "case 3\n" ; pivot pivot_array (k + 1) (k + l + 2) i j ; print_string "I accomplished the pivot \n"; simplex_rec pivot_array k l
      |_ -> print_string "case 4\n" ; Infty
  in simplex_rec pivot_array k l


(***** Test *****)

let a1 = [|[| foi 2 ; foi 3 ; foi 4 |] ; [|foi 3 ; foi 2 ; foi 1 |] ; [|foi 2 ; foi 5 ; foi 3 |]|]
let b1 = [| foi 0 ; foi 10 ; foi 15 |]
let k1 = 2
let l1 = 2

(* let x = simplex a1 b1 k1 l1 *)

let a2 = [|[| foi 1000 ; foi 1200 |] ; [|foi 10 ; foi 5 |] ; [| foi 2 ; foi 3 |] ; [| foi 1 ; foi 0 |] ; [| foi 0 ; foi 1 |]|]
let b2 = [| foi 0 ; foi 200 ; foi 60 ; foi 34 ; foi 14 |]

let k2 = 4
let l2 = 1
	    
let x = simplex a2 b2 k2 l2


let () = print_string "The result is : " ; print_frac x
