(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "igraph.sats"

(* ****** ****** *)

//
// remove those registers that cannot be used
// for general purpose (e.g., SP and FP)
//
fun igraph_simplify0 (ig: igraph_t): void

(* ****** ****** *)

//
// remove nodes that have degrees strictly less
// that K, where K is the number of available
// general-purpose registers
//
fun igraph_simplify1 (ig: igraph_t): void

(* ****** ****** *)

(* end of [regalloc.sats] *)
