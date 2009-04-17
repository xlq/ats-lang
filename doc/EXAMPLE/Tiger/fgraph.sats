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

staload "gnode.sats"

(* ****** ****** *)

abstype fgnodeinfo_t // information stored at each node

fun fgnodeinfo_pred_get (info: fgnodeinfo_t): gnodelst_t
fun fgnodeinfo_succ_get (info: fgnodeinfo_t): gnodelst_t

fun fgnodeinfo_make
  (gn: gnode_t, uselst: $TL.templst, deflst: $TL.templst): fgnodeinfo_t
// end of [fgnodeinfo_make]

(* ****** ****** *)

fun fprint_fgnodeinfo (out: FILEref, info: fgnodeinfo_t): void

fun print_fgnodeinfo (info: fgnodeinfo_t): void
fun prerr_fgnodeinfo (info: fgnodeinfo_t): void

(* ****** ****** *)

abstype fgraph_t (int) // a boxed type
typedef fgraph0 = [n:nat] fgraph_t (n)

(* ****** ****** *)

fun fprint_fgraph (out: FILEref, fg: fgraph0): void

(* ****** ****** *)

fun fgraph_empty (): fgraph_t 0

fun fgraph_nodeinfo_get (fg: fgraph0, n: gnode_t): fgnodeinfo_t

fun fgraph_node_succlst_get (fg: fgraph0, n: gnode_t): gnodelst_t
fun fgraph_node_predlst_get (fg: fgraph0, n: gnode_t): gnodelst_t

(* ****** ****** *)

fun fgraph_extend {n:nat}
  (fg: fgraph_t n, n: int n, info: fgnodeinfo_t): fgraph_t (n+1)
// end of [fgraph_extend]

(* ****** ****** *)

fun fgraph_edge_insert (fg: fgraph0, fr: gnode_t, to: gnode_t): void
fun fgraph_edge_remove (fg: fgraph0, fr: gnode_t, to: gnode_t): void

(* ****** ****** *)

fun fgraph_make_instrlst (inss: $AS.instrlst): fgraph0

(* ****** ****** *)

(* end of [fgraph.sats] *)
