(*
** some code for testing the forlist syntax
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: November, 2010
//
(* ****** ****** *)

staload "prelude/SATS/syndef.sats"
staload _(*anon*) = "prelude/DATS/syndef.dats"

(* ****** ****** *)

(*
for_list (x:T) `in` xs `do` $exp =>
  forlist_in_do<T> (xs, lam (x) => $exp)
*)

(* ****** ****** *)

#define :: list_cons

typedef intlst = List (int)

val xs = (
  0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: list_nil
) : intlst // end of [val]

val () = for_list!
  (x:int) `in` xs do (
  print "x = "; print x; print_newline ()
) // end of [val]

implement main () = ()

(* ****** ****** *)

(* end of [forlist.dats] *)

////

for_list (x:int) `in` $exp do (sum := sum + x) =>

 let
    var x: int
    var xs: list(int) = exp
 in
   while (list_isnot_null (xs)) {
     val () = list_uncons (xs, x); val () = $exp
   } // end of [while]
 end // end of [let]