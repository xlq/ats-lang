(*
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October, 2011
//
*)

(* ****** ****** *)

staload LS = "libats/SATS/linordset_randbst.sats"
staload _(*anon*) = "libats/DATS/linordset_randbst.dats"

(* ****** ****** *)

staload Time = "libc/SATS/time.sats"
staload Rand = "libc/SATS/random.sats"

(* ****** ****** *)

implement
$LS.compare_elt_elt<int> (x1, x2, _(*cmp*)) =
  if x1 < x2 then ~1 else if x1 > x2 then 1 else 0

implement
main (argc, argv) = let
  var n: int = 0
  val () = begin
    if argc >= 2 then n := int_of_string (argv.[1])
  end // end of [val]
  val [n:int] n = int1_of n; val n2 = n / 2
  val () = assert (n > 0)
  val () = $Rand.srand48_with_time ()
  fn cmp (x1: int, x2: int):<cloref> Sgn = compare (x1, x2)
//
  val rng = $LS.linordset_rngobj_make_drand48 ()
//
  var ints1: $LS.set (int) = $LS.linordset_make_nil ()
  var i: int; val () =
    for (i := 0; i < n2; i := i+1) {
      val _ = $LS.linordset_insert<int> (rng, ints1, $Rand.randint n, cmp)
    }
  // end [val]
//
  val size1 = $LS.linordset_size (ints1)
  val () = begin
    print "size1 = "; print size1; print_newline ()
  end
  val height1 = $LS.linordset_height (ints1)
  val () = begin
    print "height1 = "; print height1; print_newline ()
  end // end of [val]
//
  val () = $LS.linordset_free (ints1)
//
  val () = $LS.linordset_rngobj_free (rng)
//
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [libats_linordset_randbst.dats] *)
