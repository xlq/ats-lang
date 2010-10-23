//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

(* ****** ****** *)

// imperative style
fun tally1 (n: int): int = let
  var i: int // uninitialized
  var res: int = 0
in
  for (i := 1; i <= n; i := i + 1) res := res + i;
  res
end // end of [tally]

// functional style
fun tally2
  (n: Nat): int = loop (0, n, 1) where {
  fun loop (res: int, n: int, i: int): int =
    if i <= n then loop (res + i, n, i + 1) else res
} // end of [tally2]

implement main () = let
  val ans1 = tally1 (100)
  val ans2 = tally2 (100)
in
  printf ("tally(100) = %i\n", @(ans1));
  printf ("tally(100) = %i\n", @(ans2));
end // end of [main]

(* ****** ****** *)

(* end of [tally.dats] *)
