(*
// some testing code for functions declared in
// prelude/SATS/dlist_vt.sats
*)

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Spring, 2009

(* ****** ****** *)

staload RAND = "libc/SATS/random.sats"
staload STDLIB = "libc/SATS/stdlib.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/unsafe.dats"
staload _(*anonymous*) = "prelude/DATS/dlist_vt.dats"

(* ****** ****** *)

#define MAXELT 100

fun dlist_randgen
  {n:nat} (n: int n)
  : dlist_vt (int, 0, n) =
  if n > 0 then let
    val i =  $RAND.randint (MAXELT)
  in
    dlist_vt_cons (i, dlist_randgen (n-1))
  end else dlist_vt_nil ()
// end of [dlist_randgen]

(* ****** ****** *)

implement
main (argc, argv) = let
  #define N 100
  val xs = dlist_randgen (N)
  val n: int(N) = dlist_vt_length_r (xs)
  val () = assertloc (n = N)
  val xs = dlist_vt_move_end (xs)
  val _1: int(1) = dlist_vt_length_r (xs)
  val () = assertloc (_1 = 1)
  val _1n: int(N-1) = dlist_vt_length_f (xs)
  val () = assertloc (_1n = N-1)
  val xs = dlist_vt_move_beg (xs)
  val xs = dlist_vt_insert (xs, 0)
  val _n1: int(N+1) = dlist_vt_length_r (xs)
  val () = assertloc (_n1 = N+1)
  val () = dlist_vt_free (xs)
in
  print "The run of [prelude_dlist.dats] is done successfully!\n"
end // end of [main]

(* ****** ****** *)

(* end of [prelude_dlist_vt.dats] *)
