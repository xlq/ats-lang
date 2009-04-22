(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload TL = "templab.sats"

(* ****** ****** *)

staload "fgraph.sats"
staload "igraph.sats"

(* ****** ****** *)

//
// remove those registers that cannot be used
// for general purpose (e.g., SP and FP)
//
fun igraph_simplify0 (ig: igraph_t): void

(* ****** ****** *)

// the returned list gives an order to be used for selecting
fun igraph_regalloc (ig: igraph_t): $TL.templst // registers

(* ****** ****** *)

(* end of [regalloc.sats] *)
