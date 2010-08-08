(*
** some testing code for functions declared in
** libc/SATS/gmp.sats
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Author: Shivkumar Chandrasekaran (shiv AT ece DOT ucsb DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/pointer.dats"

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

fun mpz_test
  (): void = () where {
  #define PI 31415927
  #define SQRT2 141421
//
  var x: mpz_vt
  val () = mpz_init (x)
  val () = mpz_set (x, PI)
  val () = assert (mpz_get_int (x) = PI)
  val () = mpz_clear (x)
//
  val (pfx_gc, pfx | px) = ptr_alloc<mpz_vt> ()
  val () = mpz_init2 (!px, 64UL); val () = mpz_set (!px, SQRT2)
  val () = assert (mpz_get_int (!px) = SQRT2)
  val () = mpz_clear (!px)
  val () = ptr_free (pfx_gc, pfx | px)
//
} // end of [mpz_test]

(* ****** ****** *)

fun mpf_test
  () = () where {
//
  #define fPI 3.1415926535898
//
  var x : mpf_vt and y : mpf_vt
  var z : mpf_vt
//
  val () = mpf_set_default_prec (128UL)
  val () = mpf_init (x)
  val () = assert (mpf_get_prec (x) = 128UL)
  val () = mpf_set_prec (x, 128UL)
  val () = mpf_set_d (x, fPI)
  val () = assert (mpf_get_d (x) = fPI)
//
  val () = mpf_init2 (y, 256UL)
  val () = mpf_set_d (y, 4*fPI)
  val () = assert (mpf_get_d (y) = 4*fPI)
//
  val () = mpf_init_set (z, y)
  val () = mpf_add2 (z, 123456789UL)
  val () = mpf_sub2 (z, 123456789UL)
  val () = assert (mpf_get_d (y) = mpf_get_d (z))
//
  val () = mpf_add3 (z, x, y)
  val () = mpf_mul3 (x, z, y)
  val () = mpf_div3 (z, x, y)
  val () = mpf_sqrt (y, x)
(*
  val () = printf (
    "x = %g, y = %g, z = %g\n", @(mpf_get_d (x), mpf_get_d (y), mpf_get_d (z))
  ) // end of [val]
*)
  val () = mpf_clear (z)
  val () = mpf_clear (y)
  val () = mpf_clear (x)
} // end of [mpf_test]

(* ****** ****** *)

implement
main () = () where {
//
  val () = mpz_test ()
//
  val () = mpf_test ()
//
  val () = print "[libc_gmp.dats] testing passes!\n"
} // end of [main]

(* ****** ****** *)

(* end of [libc_gmp.dats] *)
