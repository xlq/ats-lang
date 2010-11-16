(*
** some code for testing the "for ... in_range ... do ..." syntax
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: November, 2010
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array0.dats"

(* ****** ****** *)

staload "prelude/SATS/syndef.sats"
staload _(*anon*) = "prelude/DATS/syndef.dats"
local #include "prelude/HATS/syndef.hats" in (*empty*) end

(* ****** ****** *)

(*
for! (x) in_range $exp1 do $exp2 =>
  let
    val (start, finish, stride) = $exp1
    var x: int = 0
  in
    for (x := start; x < finish; x := x + stride) $exp2
  end
*)

(* ****** ****** *)

#define :: list_cons
typedef intlst = List (int)

(* ****** ****** *)

val xs = array0_make_arrsz
  {int} ($arrsz (tupz! 1 2 3 4 5 6 7 8 9 10))
val _0 = size1_of_int1 (0)
var prod: int = 1
val nxs = array0_size (xs)
val () = for!
  (i:size_t) in_range (nxs) do {
  val x = xs[i]
  val () = if i >= 1 then print "," else ()
  val () = print x
  val () = prod := prod * x
} // end of [val]
val () = print_newline ()
val () = println! ("The product of the array = ", prod)

implement main () = ()

(* ****** ****** *)

(* end of [forrange.dats] *)
