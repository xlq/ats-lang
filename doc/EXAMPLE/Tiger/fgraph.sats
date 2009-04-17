(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

// directional graph for liveness analysis

(* ****** ****** *)

staload AS = "assem.sats"
staload TL = "templab.sats"

(* ****** ****** *)

staload "fgnode.sats"

(* ****** ****** *)

abstype fgnodeinfo_t // information stored at each node

fun fgnodeinfo_pred_get (info: fgnodeinfo_t): fgnodelst_t
fun fgnodeinfo_succ_get (info: fgnodeinfo_t): fgnodelst_t

fun fgnodeinfo_make
  (fgn: fgnode_t, uselst: $TL.templst, deflst: $TL.templst): fgnodeinfo_t
// end of [fgnodeinfo_make]

(* ****** ****** *)

fun fprint_fgnodeinfo (out: FILEref, info: fgnodeinfo_t): void

fun print_fgnodeinfo (info: fgnodeinfo_t): void
fun prerr_fgnodeinfo (info: fgnodeinfo_t): void

(* ****** ****** *)

abstype fgraph_t

(* ****** ****** *)

fun fprint_fgraph (out: FILEref, fg: fgraph_t): void

(* ****** ****** *)

fun fgraph_make_elt {n:nat} (n: int n, info: fgnodeinfo_t): fgraph_t

(* ****** ****** *)

fun fgraph_size (fg: fgraph_t): size_t

(* ****** ****** *)

fun fgraph_nodeinfo_get (fg: fgraph_t, n: fgnode_t): fgnodeinfo_t

fun fgraph_nodeinfo_set (fg: fgraph_t, n: fgnode_t, info: fgnodeinfo_t): void

fun fgraph_node_succlst_get (fg: fgraph_t, n: fgnode_t): fgnodelst_t
fun fgraph_node_predlst_get (fg: fgraph_t, n: fgnode_t): fgnodelst_t

(* ****** ****** *)

fun fgraph_edge_insert (fg: fgraph_t, fr: fgnode_t, to: fgnode_t): void
fun fgraph_edge_remove (fg: fgraph_t, fr: fgnode_t, to: fgnode_t): void

(* ****** ****** *)

fun fgraph_make_instrlst (inss: $AS.instrlst): fgraph_t

(* ****** ****** *)

(* end of [fgraph.sats] *)
