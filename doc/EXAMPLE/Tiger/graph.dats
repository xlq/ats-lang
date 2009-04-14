(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "graph.sats"

(* ****** ****** *)

assume node_t = int

implement eq_node_node (n1, n2) = eq_int_int (n1, n2)

(* ****** ****** *)

datatype noderep =
  | NODEsome of (node_t, nodelst(*pred*), nodelst(*succ*))
  | NODEnone of ()

(* ****** ****** *)

staload "LIB/funarray.dats"

(* ****** ****** *)

datatype graph = {n:nat} GRAPH of (funarray_t (noderep, n), int n)

(* ****** ****** *)

assume graph_t = graph

(* ****** ****** *)

implement graph_nodes_get (G) = let
  val+ GRAPH {n} (A, sz) = G
  var res: nodelst_vt = list_vt_nil ()
  var i: int; val () = for* {i:int | ~1 <= i; i < n} .<i+1>.
    (i: int i) => (i := sz-1; i >= 0; i := i-1) begin case+ A[i] of
    | NODEsome (node, _, _) => (res := list_vt_cons {node_t} (node, res))
    | NODEnone _ => ()
  end // end of [val]
in
  res
end // end of [graph_nodes_get]
 
implement graph_node_pred (G, n) = let
  val+ GRAPH {n} (A, sz) = G
  val n = int1_of_int (n)
  val () = assert_errmsg (n < sz, "graph_node_pred: upper violation")
  val () = assert_errmsg (0 <= n, "graph_node_pred: lower violation")
in
  case+ A[n] of
  | NODEsome (_, pred, _) => pred | NODEnone () => '[]
end // end of [graph_node_pred]

implement graph_node_succ (G, n) = let
  val+ GRAPH {n} (A, sz) = G
  val n = int1_of_int (n)
  val () = assert_errmsg (n < sz, "graph_node_succ: upper violation")
  val () = assert_errmsg (0 <= n, "graph_node_succ: lower violation")
in
  case+ A[n] of
  | NODEsome (_, _, succ) => succ | NODEnone () => '[]
end // end of [graph_node_succ]

implement graph_node_adjlst (G, n) = let
  val+ GRAPH {n} (A, sz) = G
  val n = int1_of_int (n)
  val () = assert_errmsg (n < sz, "graph_node_adjlst: upper violation")
  val () = assert_errmsg (0 <= n, "graph_node_adjlst: lower violation")
in
  case+ A[n] of
  | NODEsome (_, pred, succ) => pred + succ | NODEnone () => '[]
end // end of [graph_node_adjlst]

(* ****** ****** *)

(*
fun graph_make (): graph_t
fun graph_node_make (): node_t
fun graph_edge_insert (fr: node_t, to: node_t): void
fun graph_edge_remove (fr: node_t, to: node_t): void

fun node_name_get (n: node): string
*)

(* ****** ****** *)

(* end of [graph.dats] *)
