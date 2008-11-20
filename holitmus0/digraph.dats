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

staload "digraph.sats"

(* ****** ****** *)

implement print_digraph (x) = print_mac (fprint_digraph, x)
implement prerr_digraph (x) = prerr_mac (fprint_digraph, x)

(* ****** ****** *)

(* end of [digraph.dats] *)
