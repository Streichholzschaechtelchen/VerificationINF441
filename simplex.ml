module Fraction =
  struct
    type frac = |Frac of int * int |Infty |Void

    let foi n = Frac (n, 1)

    let rec pgcd a b = match b with
      |0 -> abs a
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
      |Void, _                -> true
      |_, Infty               -> true
      |Infty, _               -> false
      |Frac(a, b), Frac(c, d) -> a * d >= b * c
      |_                      -> false

    let eq x y = match x, y with
      |Infty, Infty |Void, Void            -> true
      |Infty, _ |_, Infty |Void, _|_, Void -> false
      |Frac(a, b), Frac(c, d)              -> a * d = b * c

    let print_frac x = match x with
      |Frac(a, b) -> print_int a ; print_string " / " ; print_int b
      |Infty -> print_string "Infty"
      |Void -> print_string "Void"
  end

open Fraction

let array_foi a =
  let n = Array.length a in
  let frac_a = Array.make n (foi 0) in
  for i = 0 to n - 1 do
    frac_a.(i) <- foi a.(i)
  done;
  frac_a

let matrix_foi a =
  let n = Array.length a in
  let frac_a = Array.make n ([|foi 0|]) in
  for i = 0 to n - 1 do
    frac_a.(i) <- array_foi a.(i)
  done;
  frac_a

let print_array a =
  let n = Array.length a in
  for i = 0 to n - 1 do
    print_frac a.(i); print_string " ; "
  done;
  print_string "\n"

let print_matrix a = let n = Array.length a in
  for i = 0 to n - 1 do
    print_array a.(i);
  done

let is_base_column a n m j0 i0 = (* checks if column j0 has only zeros and one 1 from idex i0*)
  let count = ref 0 in
  let nonzero_line = ref None in
  let i = ref i0 in
  while !i < n && (eq a.(!i).(j0) (foi 0) || eq a.(!i).(j0) (foi 1)) do
    if eq a.(!i).(j0) (foi 1) then (count := !count + 1 ; nonzero_line := Some (!i));
    i := !i + 1
  done;
  print_string "checked column, found i = " ; print_int !i ; print_string  " and count = " ; print_int !count ; print_string "\n";
  if !i = n && !count = 1 then !nonzero_line else None


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

let find_pivot a n m =
  let j = ref 0 in
  while !j < (m - 1) && pos (opp a.(0).(!j)) do j := !j + 1 done;
  if !j = m - 1 then None else
  (print_string "I found a strictly positive column and it is "; print_int !j; print_string "\n";
  let i = ref 1 in
  let lig = ref None in
  while !i < n do
    if not (pos (opp a.(!i).(!j))) then (print_string "I found a positive one \n" ; match !lig with
      |None -> lig := Some !i
      |Some i0 -> let c = pos (sum (prod (inv a.(i0).(!j)) a.(i0).(m - 1)) (opp (prod (inv a.(!i).(!j)) a.(!i).(m - 1)))) in if c then lig := Some !i
    );
    i := !i + 1;
    (* raise (Failure "begin"); *)
  done;
  Some(Some !j, !lig))

(* Solve the simplex when b has all coordinates positive *)
let init_simplex_aux ab k l =
  let pivot_array = Array.make (k + 1) [||] in
  for i = 0 to k do
    let idlig = Array.make k (foi 0) in
    if i > 0 then idlig.(i - 1) <- (foi 1);
    pivot_array.(i) <- Array.append idlig ab.(i)
  done;
  pivot_array

let init_simplex a b k l =
  let ab = Array.make (k + 1) [||] in
  for i = 0 to k do
    ab.(i) <- Array.append a.(i) [|b.(i)|]
  done;
  init_simplex_aux ab k l


let sum_line a m n i0 i1 lambda = (* a frac array of size m * n, adds lambda * line i1 to line i0  *)
  for j = 0 to n - 1 do
    a.(i0).(j) <- sum (a.(i0).(j)) (prod (a.(i1).(j)) lambda)
  done

let prod_line a m n i0 lambda = (* a frac array of size m * n, multiplies line i0 by lambda *)
  for j = 0 to n - 1 do
    a.(i0).(j) <- prod lambda a.(i0).(j)
  done


let simplex_basis pivot_array k l =
  print_string "Enter simplex \n";
  (* let pivot_array = init_simplex a b k l in *)
  print_string "Aux array created and is \n" ; print_matrix pivot_array ;
  let rec simplex_rec pivot_array k l =
    print_string "Enter recursion\n";
    let piv = find_pivot pivot_array (k + 1) (k + l + 2) in match piv with
      |None -> print_string "case 1\n" ; pivot_array.(0).(k + l + 1)
      |Some (_, None) -> print_string "case 2\n" ; Infty
      |Some (Some j, Some i) ->
        print_string "I chose line " ; print_int (i); print_string "\n";
        print_string "case 3\n" ; pivot pivot_array (k + 1) (k + l + 2) i j ; print_string "I accomplished the pivot \n"; simplex_rec pivot_array k l
      |_ -> print_string "case 4\n" ; Infty
  in simplex_rec pivot_array k l


let simplex a b k l =
  (* print_string "Enter simplex_gen \n"; *)
  let pivot_array = init_simplex a b k l in
  let count = ref 0 in
  for i = 1 to k do
    if not (pos b.(i)) then (
      count := !count + 1;
      for j = 0 to k + l + 1 do
        pivot_array.(i).(j) <- opp pivot_array.(i).(j)
      done
    )
  done;
  print_string "Found " ; print_int !count ; print_string " non positive numbers \n";
  if !count = 0 then simplex_basis pivot_array k l
  else(
    (* Add more variables to each line and minimize their sum*)
    let original_form = Array.copy pivot_array.(0) in
    pivot_array.(0) <- Array.make (k + l + 2) (foi 0);
    (* for j = 0 to k do
      pivot_array.(0).(j) <- foi (-1)
    done; *)
    (* for i = 1 to k do
      pivot_array.(i) <- Array.append [|foi 0 |] pivot_array.(i)
    done; *)
    print_string "The first line is " ; print_array pivot_array.(0) ; print_string "\n";
    (* print_string "The pivot_array is " ; print_matrix pivot_array ; print_string "\n"; *)
    (* print_string "The intermediate pivot_array (before normalization) is " ; print_matrix pivot_array ; print_string "\n"; *)
    for i = 1 to k do
      sum_line pivot_array (k + 1) (k + l + 2) 0 i (foi (1))
      (* if pivot_array.(i).(i - 1) = foi 1 then sum_line pivot_array (k + 1) (k + l + 2) 0 i (foi 1);
      print_string "Done first \n";
      if pivot_array.(i).(i - 1) = foi (-1) then sum_line pivot_array (k + 1) (k + l + 2) 0 i (foi (-1)); *)
    done;
    print_string "The intermediate pivot_array (after normalization) is \n" ; print_matrix pivot_array ; print_string "\n";
    let feasibility_pivot_array = init_simplex_aux pivot_array k (k + l) in
    let feasible = simplex_basis feasibility_pivot_array k (k + l) in
    print_string "feasible is " ; print_frac feasible ; print_string "\n";
    if not (eq feasible (foi 0)) then Void
    else(
      (* check that no t is a base column *)
      for j = 0 to (k - 1) do
        print_string "checking the ts \n";
        match is_base_column feasibility_pivot_array (k + 1) (k + 2 * l + 2) j 0 with
          |None -> ()
          |Some i0 ->
            print_string "found a base column \n";
            let flag = ref true in
            let jj = ref k in
            while !flag && !jj < (k + 2 * l + 2) do
              if (not (eq feasibility_pivot_array.(i0).(!jj) (foi 0))) && (is_base_column feasibility_pivot_array (k + 1) (k + 2 * l + 2) !jj 0) = None then (
                pivot feasibility_pivot_array (k + 1) (k + 2 * l + 2) i0 !jj;
                flag := false
              );
              jj := !jj + 1
            done
      done;
      print_string "checked that no t is a base column \n";
      (* go back to the original simplex problem *)
      pivot_array.(0) <- original_form;
      for i = 1 to k do
        pivot_array.(i) <- Array.sub feasibility_pivot_array.(i) k (k + l + 2)
      done;
      print_string "Looking for base columns \n";
      for j = 0 to (k + l) do
        match is_base_column pivot_array (k + 1) (k + l + 2) j 1 with
          |None -> ()
          |Some i0 ->
            print_string "found a base column \n";
            pivot pivot_array (k + 1) (k + l + 2) i0 j
      done;
      (* lauch the simplex algorithm *)
      simplex_basis pivot_array k l
      (* let final_pivot_array = Array.make (k + 1) [||] in
      for i = 0 to k do
        final_pivot_array.(i) <- Array.sub feasibility_pivot_array.(i) (k + 1) (k + l + 2)
      done;
      if final_pivot_array.(0).(0) != foi 0 then prod_line final_pivot_array (k + 1) (k + l + 2) 0 (opp final_pivot_array.(0).(0))
      else(
        let check = ref false in
        let i = ref 1 in
        while not !check && !i <= k do (* possibility to have b0 < 0, normally not a problem *)
          if final_pivot_array.(!i).(0) = foi 0 then (
            sum_line final_pivot_array (k + 1) (k + l + 2) 0 !i (opp final_pivot_array.(!i).(0));
            check := true;
            i := !i + 1
          )
        done
      );
      (* possibility to have final_pivot_array.(0).(0) = 0 if precedent loop found no nonzero line *)
      simplex_basis pivot_array k l *)
    )
  )


(***** Test ****)

(*let a = [| [| foi (-1) ; foi 0 ; foi 0 ; foi 1 ; foi 0 ; foi 0 |];
[|foi (-1)  ; foi 1  ; foi 0  ; foi 1  ; foi (-1)  ; foi 0  |];
[|foi 1  ; foi (-1)  ; foi 0  ; foi (-1)  ; foi 1  ; foi 0  |];
[|foi 0  ; foi 0  ; foi 1  ; foi 0  ; foi 0  ; foi (-1)  |];
[|foi 0  ; foi 0  ; foi (-1)  ; foi 0  ; foi 0  ; foi 1  |];
[|foi 1  ; foi 0  ; foi 0  ; foi (-1)  ; foi 0  ; foi 0  |];
[|foi (-1)  ; foi 0  ; foi 0  ; foi 1  ; foi 0  ; foi 0  |];
[|foi 1  ; foi 0  ; foi 0  ; foi (-1)  ; foi 0  ; foi 0 |];|]

let b = [|foi (-1)  ; foi 0  ; foi 0  ; foi 0  ; foi 0  ; foi (-1)  ; foi 0  ; foi (-1)|]

let k = 7
let l = 5

let x = simplex a b k l

let () = print_string "The result is : " ; Fraction.print_frac x

let a = [| [| foi 1 ; foi 0 ; foi 0 ; foi (-1) ; foi 0 ; foi 0 |];
[|foi (-1)  ; foi 1  ; foi 0  ; foi 1  ; foi (-1)  ; foi 0  |];
[|foi 1  ; foi (-1)  ; foi 0  ; foi (-1)  ; foi 1  ; foi 0  |];
[|foi 0  ; foi 0  ; foi 1  ; foi 0  ; foi 0  ; foi (-1)  |];
[|foi 0  ; foi 0  ; foi (-1)  ; foi 0  ; foi 0  ; foi 1  |];
[|foi 1  ; foi 0  ; foi 0  ; foi (-1)  ; foi 0  ; foi 0  |];
[|foi (-1)  ; foi 0  ; foi 0  ; foi 1  ; foi 0  ; foi 0  |];
[|foi 1  ; foi 0  ; foi 0  ; foi (-1)  ; foi 0  ; foi 0 |];|]

let b = [|foi 1  ; foi 0  ; foi 0  ; foi 0  ; foi 0  ; foi (-1)  ; foi 0  ; foi (-1)|]

let k = 7
let l = 5

let x = simplex a b k l

let () = print_string "The result is : " ; Fraction.print_frac x

let a1 = [|[| foi 2 ; foi 3 ; foi 4 |] ; [|foi 3 ; foi 2 ; foi 1 |] ; [|foi 2 ; foi 5 ; foi 3 |]|]
let b1 = [| foi 0 ; foi 10 ; foi 15 |]
let k1 = 2
let l1 = 2

let x = simplex a1 b1 k1 l1

let () = print_string "The result is : " ; Fraction.print_frac x

let a2 = [|[| foi 1000 ; foi 1200 |] ; [|foi 10 ; foi 5 |] ; [| foi 2 ; foi 3 |] ; [| foi 1 ; foi 0 |] ; [| foi 0 ; foi 1 |]|]
let b2 = [| foi 0 ; foi 200 ; foi 60 ; foi 34 ; foi 14 |]

let k2 = 4
let l2 = 1

let x = simplex a2 b2 k2 l2

let () = print_string "The result is : " ; print_frac x*)
