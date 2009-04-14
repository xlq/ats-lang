(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

abstype graph_t
abst@ype node_t = $extype "ats_int_type"
typedef nodelst = List (node_t)
viewtypedef nodelst_vt = List_vt (node_t)

fun graph_nodes_get (G: graph_t): nodelst_vt
fun graph_node_succ (G: graph_t, n: node_t): nodelst
fun graph_node_pred (G: graph_t, n: node_t): nodelst
fun graph_node_adjlst (G: graph_t, n: node_t): nodelst // pred+succ
fun eq_node_node (n1: node_t, n2: node_t): bool

fun graph_make (): graph_t
fun graph_node_make (): node_t
fun graph_edge_insert (fr: node_t, to: node_t): void
fun graph_edge_remove (fr: node_t, to: node_t): void

fun node_name_get (n: node_t): string

(* ****** ****** *)

(* end of [graph.sats] *)
