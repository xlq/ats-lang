(*
**
** HOLITMUS: a proof checker
**
** Originally implemented in OCaml
**    by Chad Brown (cebrown AT mathgate DOT info)
** Time March/September, 2008
**
** Translated to ATS
**    by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: November, 2008
**
*)

(* ****** ****** *)

abstype digraph (int(*row*), int(*col*))
abstype digraph = [m,n:nat] digraph (m, n)

fun digraph_nil {m,n:nat} (): digraph (m, n)

fun fprint_digraph {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: digraph): void

fun print_digraph (_: digraph): void
fun prerr_digraph (_: digraph): void

(* ****** ****** *)

(* end of [digraph.sats] *)
