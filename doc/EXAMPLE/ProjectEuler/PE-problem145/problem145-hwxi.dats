//
// ProjectEuler: Problem 145
// How many reversible numbers are below one-billion?
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

fun reverse
  (x: ulint): ulint = let
  fun loop (x: ulint, sum: ulint): ulint =
    if x > 0UL then let
      val r = x mod 10UL in loop (x / 10UL, 10UL * sum + r)
    end else sum
in
  loop (x, 0UL)
end // end of [reverse]

fun revtest (x: ulint): bool =
  if x > 0UL then let
    val r = x mod 2UL in if r >= 1UL then revtest (x / 10UL) else false
  end else true
// end of [revtest]

(* ****** ****** *)

implement main () = let
  fun loop (
      i: ulint, N: ulint, c: &int
    ) : void =
    if i < N then (
      if i mod 10UL > 0UL then let
        val sum = i + reverse (i)
        val () = if revtest (sum) then c := c + 1
      in
        loop (i+1UL, N, c)
      end else
        loop (i+1UL, N, c)
      // end of [if]
    ) // end of [if]
  // end of [loop]
  var c: int = 0
  val () = loop (1UL, 1000UL, c)
  val ans = c
  val () = (print "ans(1000) = "; print ans; print_newline ())
  val () = c := 0
  val () = loop (1UL, 1000000000UL, c)
  val ans = c
  val () = assert_errmsg (ans = 608720, #LOCATION)
  val () = (print "ans(1000000000) = "; print ans; print_newline ())
in
  // nothing
end // end of [mail]

(* ****** ****** *)

(* end of [problem145-hwxi.dats] *)
