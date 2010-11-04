(*
** some code for testing the forlist syntax
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: November, 2010
//
(* ****** ****** *)

staload "prelude/DATS/list.dats"

(* ****** ****** *)

(*
ifor_list (i) (x:T) `in` xs `do` $exp =>
  list_iforeach_cloptr__viewless<T> (xs, lam (x) => $exp)
*)

(* ****** ****** *)

#define :: list_cons

typedef intlst = List (int)

val xs = (
  0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: list_nil
) : intlst // end of [val]

val () = `ifor_list`
  (i) (x:int) `in` xs `do` (if i > 0 then print ","; print x)
val () = print_newline ()

implement main () = ()

(* ****** ****** *)

(* end of [forlist.dats] *)
