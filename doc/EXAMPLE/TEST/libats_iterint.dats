(*
** some testing code for functions declared in
** libats/SATS/iterint.sats
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Spring, 2009
//

(* ****** ****** *)

staload "libats/SATS/iterint.sats"

(* ****** ****** *)

fn sum {n:nat} (n: int n): Nat = res where {
  stadef n1 = n + 1
  var res: Nat = 0
  viewdef v = Nat @ res
  var !p_f = @lam
    (pf: !v | i: natLt n1): void =<clo> res := res + i
  // end of [var]
  val () = foreach_clo {v} {n1} (view@ res | n + 1, !p_f)
} // end of [sum]

(* ****** ****** *)

dynload "libats/DATS/iterint.dats"

implement main () = let
  val sum100 = sum (100)
in
  print "sum100 (5050) = "; print sum100; print_newline ()
end // end of [main]

(* ****** ****** *)

(* end of [libats_iterint.dats] *)

