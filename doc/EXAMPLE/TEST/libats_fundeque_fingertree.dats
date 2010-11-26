(*
** some testing code for functions declared in
** libats/SATS/fundeque_fingertree.sats
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: November, 2010
//
(* ****** ****** *)

staload DQ = "libats/SATS/fundeque_fingertree.sats"
staload _(*anon*) = "libats/DATS/fundeque_fingertree.dats"
stadef deque = $DQ.deque

(* ****** ****** *)

implement
main (argc, argv) = {
//
  macdef N = 10
  val N = (if argc >= 2 then int_of (argv.[1]) else N): int
//
  typedef ideque = [n:nat] $DQ.deque (int, n)
//
  val t = $DQ.fundeque_nil ()
  val t1 = loop (0, t) where {
    fun loop (n: int, res: ideque):<cloref1> ideque =
      if n < N then loop (n+1, $DQ.fundeque_cons (n, res)) else res
    // end of [loop]
  } // end of [val]
  val t = $DQ.fundeque_nil ()
  val t2 = loop (0, t) where {
    fun loop (n: int, res: ideque):<cloref1> ideque =
      if n < N then loop (n+1, $DQ.fundeque_snoc (res, n)) else res
    // end of [loop]
  } // end of [val]
  val t12 = $DQ.fundeque_append (t1, t2)
//
  val () = assertloc ($DQ.fundeque_size (t12) = N+N)
//
  val () = loop (t12) where {
    fun loop (t: ideque): void =
      if $DQ.fundeque_is_nil (t) then ()
      else let
        var x: int
        val t = $DQ.fundeque_uncons (t, x)
        val () = print (x)
      in
        loop (t)
      end // end of [if]
  } // end of [val]
  val () = print_newline ()
//
  val () = loop (t12) where {
    fun loop (t: ideque): void =
      if $DQ.fundeque_is_nil (t) then ()
      else let
        var x: int
        val t = $DQ.fundeque_unsnoc (t, x)
        val () = print (x)
      in
        loop (t)
      end // end of [if]
  } // end of [val]
  val () = print_newline ()
//
  val () = $DQ.fundeque_foreach_cloref<int> (t12, lam x => $effmask_all (print(x)))
  val () = print_newline ()
  val () = $DQ.fundeque_foreach_rev_cloref<int> (t12, lam x => $effmask_all (print(x)))
  val () = print_newline ()
//
} // end of [main]

(* ****** ****** *)

(* end [libats_fundeque_fingertree.dats] *)
