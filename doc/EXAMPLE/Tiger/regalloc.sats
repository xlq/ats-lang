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

staload "tempset.sats"

staload "fgraph.sats"

staload "igraph.sats"

(* ****** ****** *)

//
// remove those registers that cannot be used
// for general purpose (e.g., SP and FP)
//
fun igraph_simplify0 (ig: igraph_t): void

(* ****** ****** *)

datatype regassgn =
  | REGASSGNsimplify of ($TL.temp_t, tempset_t)
  | REGASSGNcoalesce of ($TL.temp_t, $TL.temp_t)
  | REGASSGNspill of ($TL.temp_t, tempset_t)

typedef regassgnlst = List regassgn

fun fprint_regassgn (out: FILEref, rasgn: regassgn): void

fun fprint_regassgnlst (out: FILEref, rasgns: regassgnlst): void

(* ****** ****** *)

fun regassgn_select (rasgn: regassgn): void

(* ****** ****** *)

// the returned list gives an order to be used for selecting
fun igraph_regalloc (ig: igraph_t): regassgnlst // registers

(* ****** ****** *)

(* end of [regalloc.sats] *)
