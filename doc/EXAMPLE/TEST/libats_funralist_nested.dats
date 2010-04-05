(*
** some testing code for functions declared in
** libats/SATS/funralist_nested.sats
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: March, 2010
//

(* ****** ****** *)

staload RA = "libats/SATS/funralist_nested.sats"
staload _(*anon*) = "libats/DATS/funralist_nested.dats"
stadef ralist = $RA.list

(* ****** ****** *)

fn genlist {n:nat}
  (n: int n): ralist (int, n) = let
  fun loop {i,j:nat | i+j == n} .<i>.
    (i: int i, xs: ralist (int, j)): ralist (int, n) =
    if i > 0 then loop (i - 1, $RA.funralist_cons (i, xs)) else xs
  val xs = $RA.funralist_make_nil ()
in
  loop (n, xs)
end // end of [genlist]

(* ****** ****** *)

#define N 100 // default
implement
main (argc, argv) = () where {
  val () = gc_chunk_count_limit_max_set (~1) // infinite
  var n: int = N
  val () = begin
    if argc >= 2 then n := int_of_string (argv.[1])
  end
  val [n:int] n = (int1_of_int)n
  val () = assert_errmsg (n > 0, #LOCATION)
  val xs = genlist (n)
//
  val () = assert_errmsg (n = $RA.funralist_length xs, #LOCATION)
//
  var i: Nat = 0
  val () = for (i := 0; i < n; i := i + 1) let
    val xs = $RA.funralist_update (xs, i, i+i+1)
    val () = assert_errmsg ($RA.funralist_lookup (xs, i) = i+i+1, #LOCATION)
  in (*nothing*) end // end of [for]
} // end of [main]

(* ****** ****** *)

////

//
//
// This file is for Solution 4, BU CAS CS 520, Fall, 2008
//
//

//
// testing some of the implemented ralist operations
//
// How to compile:
//
// atscc -O3 -o test_ralist test_ralist.dats ralist.sats ralist_solution.dats
// 

staload RA = "funralist.dats"

implement main () = let
  val xs = ralist_gen (100)

  var !p_pr =
    @lam (pf: !unit_v | x: int): void =<clo> $effmask_all (print x; print_newline ())
  // end of [pr]
  prval pf = unit_v ()
  val () = $RA.ralist_foreach_clo<int> (pf | xs, !p_pr)
  prval unit_v () = pf
  val n = $RA.ralist_length<int> (xs)
  val () = begin
    print "n(100) = "; print n; print_newline ()
  end
  val x = $RA.ralist_lookup<int> (xs, 50)
  val () = begin
    print "x(51) = "; print x; print_newline ()
  end
  val xs = $RA.ralist_update<int> (xs, 50, ~51)
  val xs = $RA.ralist_update<int> (xs, 51, ~52)
  val x = $RA.ralist_lookup<int> (xs, 50)
  val () = begin
    print "x(-51) = "; print x; print_newline ()
  end
  val x = $RA.ralist_lookup<int> (xs, 51)
  val () = begin
    print "x(-52) = "; print x; print_newline ()
  end
in
  // empty
end // end [main]

(* ****** ****** *)

(* end [test_ralist.dats] *)
