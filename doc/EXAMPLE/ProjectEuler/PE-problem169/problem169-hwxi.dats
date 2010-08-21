//
// ProjectEuler: Problem 169
// Exploring the number of different ways in which a number can be expressed
// as the sum of 2's powers
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)
//
// f(x) = the number of difference ways in which x can be expressed as the sum
// of 2's powers such that each power can occur at most 2 times.
//
// g1(x) = the numer of such ways where 1 occurs 1 time
// g2(x) = the numer of such ways where 1 occurs 2 times
// g(x) = g1(x) + g2(x)
//
// So we have
// f(2x+1) = f(x)
// f(2x+2) = f(x+1) + g2(2x+2)
// g(2x+1) = f(x)
// g(2x+2) = g(x+1) + g2(x)
// g2(2x+1) = 0
// g2(2x+2) = g(x+1) + g2(x)
//
(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

(*
fun f (x: int): int =
  if x >= 2 then let
    val r = x mod 2; val x2 = x/2
  in
    if r > 0 then f (x2) else f (x2) + f (x2-1)
  end else 1 // end of [if]
// end of [f]
val ans = f (1000000000) // ans = 73411
val () = (print "ans = "; print ans; print_newline ())
*)

(* ****** ****** *)

fun pow5 (n: int): ullint = let
  fun loop (n: int, res: ullint): ullint =
    if n > 0 then loop (n-1, 5ULL * res) else res
  // end of [loop]
in
  loop (n, 1ULL)
end // end of [pow5]

fun f (x: ullint): ullint =
  if x >= 2ULL then let
    val r = x mod 2ULL; val x2 = x/2ULL
  in
    if r > 0ULL then f (x2) else f (x2) + f (x2-1ULL)
  end else 1ULL // end of [if]
// end of [f]

(*
fun f
  (x: &mpz_vt): ulint = let
  val sgn = mpz_cmp (x, 2UL)
in
  if sgn >= 0 then let
    val _r = mpz_fdiv_q (x, 2UL)
  in
    if mpz_odd_p (x) then f (x)
    else let
      var x2: mpz_vt
      val () = mpz_init (x2)
      val () = mpz_sub (x2, x, 1UL)
      val n2 = f (x2)
      val () = mpz_clear (x2)
    in
      f (x) + n2
    end // end of [if]
  end else 1UL
end // end of [f]
*)

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

implement main () = let
(*
  val x = pow5 (9)
  val () = (print "x = "; print x; print_newline ())
  val ans = f (x) + 9ULL * f (x-1ULL) // 73411
*)
  val x = pow5 (25)
  val () = (print "x = "; print x; print_newline ())
  val ans = f (x) + 25ULL * f (x-1ULL)
  val () = assert_errmsg (ans = 178653872807ULL, #LOCATION)
in
  (print "ans = "; print ans; print_newline ())
end // end of [main]

(* ****** ****** *)

(* end of [problem169-hwxi.dats] *)
