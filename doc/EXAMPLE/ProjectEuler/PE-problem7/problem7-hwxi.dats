//
// ProjectEuler: Problem 7
// Finding the 10001st prime number
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

fun loop {n:nat} .<n>.
  (n: int n, p1: &mpz_vt, p2: &mpz_vt): ulint =
  if n > 0 then let
    val () = mpz_nextprime2 (p2, p1) in loop (n-1, p2, p1)
  end else begin
    mpz_get_ulint (p1)
  end // end of [if]
// end of [loop]

(* ****** ****** *)

implement main () = () where {
  var p1: mpz_vt and p2: mpz_vt
  val () = mpz_init_set (p1, 2); val () = mpz_init (p2)
  val p = loop (6-1, p1, p2)
  val () = (print "The 6th prime number is "; print p; print_newline ())
  val p = loop (10001-1, p1, p2)
  val () = assert_errmsg (p = 104779UL, #LOCATION)
  val () = (print "The 10001st prime number is "; print p; print_newline ())
  val () = mpz_clear (p1); val () = mpz_clear (p2)
} // end of [main]

(* ****** ****** *)

(* end of [problem7.dats] *)
