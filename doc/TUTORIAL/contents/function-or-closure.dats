//
//
// code for illustration in function-or-closure.html
//
//

%{^

#include "libc/CATS/stdlib.cats"

%}

staload "libc/SATS/stdlib.sats"

(* ****** ****** *)

fn add (x: int): int -<cloref1> int =
  let fn add_x (y: int):<cloref1> int = x + y in add_x end

(* ****** ****** *)

fn test_qsort () = let

// creating a linear array of size 10
val (pf_gc, pf_A | p_A, sz_A) =
  $arrsz {int} (1, 9, 2, 8, 3, 7, 4, 6, 5, 0)

fun pr (pf: !unit_v | i: Nat, x: &int):<cloptr1> void =
  begin if i > 0 then print ", "; print x end

val () = (print "before quicksort:\n")
val () = let
  prval pf = unit_v ()
  val () = iforeach_array_ptr_tsz_cloptr {int} {unit_v} (pf | pr, !p_A, sz_A, sizeof<int>)
  prval unit_v () = pf
in
  // empty
end // end of [val]
val () = print_newline ()

val () =
  qsort {int} (!p_A, sz_A, sizeof<int>, lam (x, y) => compare (x, y))

val () = (print "after quicksort:\n")
val () = let
  prval pf = unit_v ()
  val () = iforeach_array_ptr_tsz_cloptr {int} (pf | pr, !p_A, sz_A, sizeof<int>)
  prval unit_v () = pf
in
  // empty
end // end of [val]
val () = print_newline ()

val () = array_ptr_free {int} (pf_gc, pf_A | p_A)

in

()

end

(* ****** ****** *)

fn add1 (x: int):<fun> int -<cloptr> int =
  let
    fn add1_x (y: int):<cloptr> int = x + y
  in
    add1_x
  end

(* ****** ****** *)

implement main (argc, argv) = let

val () = test_qsort ()

in

end
