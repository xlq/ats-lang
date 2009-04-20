(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload F = "frame.sats"

(* ****** ****** *)

staload "igraph.sats"

(* ****** ****** *)

staload "regalloc.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"

(* ****** ****** *)

implement igraph_simplify0
  (ig) = loop (ig, $F.theSpecialReglst) where {
  fun loop (ig: igraph_t, ts: $TL.templst): void =
    case+ ts of
    | list_cons (t, ts) => let
        val () = igraph_remove_node (ig, t) in loop (ig, ts)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
} // end of [igraph_simplify0]

(* ****** ****** *)

implement igraph_simplify1 (ig) = let
  fun loop1 (ig: igraph_t): void = let
    val ans = igraph_search_low (ig) in
    case+ ans of
    | ~Some_vt tmp => let
        val () = igraph_remove_node (ig, tmp)
      in
        loop1 (ig)
      end // end of [val]
    | ~None_vt () => ()
  end // end of [loop1]
  val () = loop1 (ig)
in
  // empty
end // end of [igraph_simplify]

(* ****** ****** *)

(* end of [regalloc.dats] *)
