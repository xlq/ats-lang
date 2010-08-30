//
// Author: Hongwei Xi (August 2007)
//

//
// How to compile:
//
// atscc -o fact1 fact1.dats
//

(* ****** ****** *)

// [fun] declares a recursive function
fun fact1 (x: int): int = if x > 0 then x * fact1 (x-1) else 1

// [fn] declares a non-recursive function
// It is fine to replace [fn] with [fun] as a non-recursive function
// is a special kind of recursive function that does not call itself.
// [@(...)] is used in ATS to group arguments for variadic functions
fn fact1_usage (cmd: string): void =
  prerrf ("Usage: %s [integer]\n", @(cmd)) // print an error message

(* ****** ****** *)

implement main (argc, argv) = begin
  if argc >= 2 then let
    val n = int_of argv.[1] // turning string into integer
    val res = fact1 n
  in
    printf ("factorial of %i = %i\n", @(n, res))
  end else begin
    fact1_usage argv.[0]; exit (1)
  end
end // end of [main]

(* ****** ****** *)

(* end of [fact1.dats] *)
