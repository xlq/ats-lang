//
// ProjectEuler: Problem 9
// Finding the sum of all numbers below 1000 that is a multiple of 3 or 5
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

// a = 2pq
// b = p^2 - q^2 // p >= q
// c = p^2 + q^2
// a+b+c = 2p(p+q) = 1000
// p(p+q) = 500 => p = 20 and q = 5

implement main () = () where {
  val a = 200
  val b = 375
  val c = 425
  val () = assert (a*a + b*b = c*c)
  val () = assert (a + b + c = 1000)
  val () = printf ("abc = %i\n", @(a*b*c))
} // end of [main]

(* ****** ****** *)

(* end of [problem9.dats] *)
