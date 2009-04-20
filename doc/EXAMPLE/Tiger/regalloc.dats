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
    val ans = igraph_search_lowdeg (ig) in
    case+ ans of
    | ~Some_vt tmp => let
        val () = igraph_remove_node (ig, tmp)
      in
        loop1 (ig)
      end // end of [Some_vt]
    | ~None_vt () => ()
  end // end of [loop1]
  fun loop2 (ig: igraph_t): void = let
    val ans = igraph_search_coalesce (ig) in
    case+ ans of
    | ~Some_vt tmptmp => let
        val tmp0 = tmptmp.0 and tmp1 = tmptmp.1
(*
        val () = begin
          prerr "igraph_simplify1: tmp0 = ";
          $TL.prerr_temp tmp0; prerr_newline ()
        end // end of [val]
        val () = begin
          prerr "igraph_simplify1: tmp1 = ";
          $TL.prerr_temp tmp1; prerr_newline ()
        end // end of [val]
*)
        val () = igraph_merge_node (ig, tmp0, tmp1)
      in
        loop1 (ig); loop2 (ig)
      end // end of [Some_vt]
    | ~None_vt () => ()
  end // end of [loop2]
  val () = loop1 (ig)
  val () = loop2 (ig)
in
  // empty
end // end of [igraph_simplify]

(* ****** ****** *)

(* end of [regalloc.dats] *)
