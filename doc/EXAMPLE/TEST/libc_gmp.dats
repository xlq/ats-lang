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
  macdef PI = 31415927U
  macdef SQRT2 = 141421UL
//
  var x: mpz_vt
  val () = mpz_init (x)
  val () = mpz_set (x, PI)
  val () = assert (mpz_sgn (x) = 1)
  val () = assert (mpz_get_uint (x) = PI)
//
  val () = mpz_set_str_exn (x, "31415927", 10)
  val () = assert (mpz_cmp (x, PI) = 0)
//
  val () = mpz_neg (x)
  val () = assert (mpz_sgn (x) = ~1)
  val () = assert (mpz_cmpabs (x, PI) = 0)
  val () = mpz_clear (x)
//
  val (pfx_gc, pfx | px) = ptr_alloc<mpz_vt> ()
  val () = mpz_init2 (!px, 64UL); val () = mpz_set (!px, SQRT2)
  val () = assert (mpz_get_ulint (!px) = SQRT2)
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
//
  val () = mpf_set_str_exn (x, "3.1415926535898", 10)
  val fx = mpf_get_d (x)
  // val () = assert (fx <> fPI) // HX: yes, they are different
  val () = assert (abs (fx - fPI) < 1E-8)
//
  var state: gmp_randstate_vt
  val () = gmp_randinit_default (state)
  val () = mpf_urandomb (x, state, 100UL)
  val () = (print "x = "; print_mpf (x, 16); print_newline ())
  val () = gmp_randclear (state)
//
  var a: mpz_vt
  val () = mpz_init_set (a, 141421)
  val () = gmp_randinit_lc_2exp (state, a, 29UL(*c*), 5UL(*m2exp*))
  val () = mpf_urandomb (x, state, 100UL)
  val () = (print "x = "; print_mpf (x, 16); print_newline ())
  val () = mpz_clear (a)
  val () = gmp_randclear (state)
//
  val _err = gmp_randinit_lc_2exp_size (state, 100UL)
  val () = mpf_urandomb (x, state, 100UL)
  val () = (print "x = "; print_mpf (x, 16); print_newline ())
  val () = gmp_randclear (state)
//
  val () = mpf_random2 (x, (mp_size_t)100, (mp_exp_t)10)
  val () = (print "x = "; print_mpf (x, 16); print_newline ())
  var exp: mp_exp_t
  val str = mpf_get_str (exp, 10, 16, x)
  val () = (print "str = "; print str; print_newline ())
  val () = strptr_free (str)
  val () = mpf_random2 (x, (mp_size_t)~100, (mp_exp_t)10)
  val () = (print "x = "; print_mpf (x, 16); print_newline ())
  val str = mpf_get_str (exp, 10, 00, x)
  val () = (print "str = "; print str; print_newline ())
  val () = strptr_free (str)
//
  val () = mpf_set_d (x, fPI)
  val () = assert (mpf_sgn (x) = 1)
  val () = assert (mpf_get_d (x) = fPI)
//
  val () = mpf_neg (x)
  val () = assert (mpf_sgn (x) = ~1)
  val () = assert (mpf_get_d (x) = ~fPI)
  val () = mpf_abs (x)
  val () = assert (mpf_get_d (x) = fPI)
//
  val () = mpf_init2 (y, 256UL)
  val () = mpf_set_d (y, 4*fPI)
  val () = assert (mpf_cmp_si (y, 12L) > 0)
  val () = assert (mpf_cmp_ui (y, 13UL) < 0)
  val () = assert (mpf_cmp_d (y, 12.56) > 0)
  val () = assert (mpf_get_d (y) = 4*fPI)
//
  val () = mpf_init_set (z, y)
  val () = mpf_add (z, 123456789UL)
  val () = mpf_sub (z, 123456789UL)
  val () = assert (mpf_get_d (y) = mpf_get_d (z))
  val () = mpf_ui_sub2 (z, 123456789UL)
  val () = mpf_ui_sub2 (z, 123456789UL)
  val () = assert (mpf_get_d (y) = mpf_get_d (z))
//
  val () = mpf_add (z, x, y)
  val () = mpf_mul (x, z, y)
  val () = mpf_div (z, x, y)
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
