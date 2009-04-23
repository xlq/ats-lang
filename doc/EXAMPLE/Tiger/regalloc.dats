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
        val () = igraph_node_remove (ig, t) in loop (ig, ts)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
} // end of [igraph_simplify0]

(* ****** ****** *)

implement igraph_regalloc (ig) = let
  typedef templst = $TL.templst
  fun loop1 (
      ig: igraph_t, res: &templst
    ) : void = let
    val ans = igraph_search_lowdeg (ig) in
    case+ ans of
    | ~Some_vt tmp => let
        val () = begin
          prerr "igraph_regalloc: loop1(simplify): tmp = ";
          $TL.prerr_temp tmp;
          prerr_newline ()
        end // end of [val]
        val () = igraph_node_remove (ig, tmp)
        val () = res := list_cons (tmp, res)
      in
        loop1 (ig, res)
      end // end of [Some_vt]
    | ~None_vt () => ()
  end // end of [loop1]
  fun loop2 (
      ig: igraph_t, res: &templst
    ) : void = let
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
        val () = igraph_node_merge (ig, tmp0, tmp1)
      in
        loop1 (ig, res); loop2 (ig, res)
      end // end of [Some_vt]
    | ~None_vt () => ()
  end // end of [loop2]
  fun loop3 (
      ig: igraph_t, res: &templst
    ) : void = let
    val ans = igraph_search_freeze (ig) in
    case+ ans of
    | ~Some_vt tmp => let
        val () = begin
          prerr "igraph_regalloc: loop3(freeze): tmp = ";
          $TL.prerr_temp tmp;
          prerr_newline ()
        end // end of [val]
        val () = igraph_node_freeze (ig, tmp)
      in
        loop1 (ig, res); loop2 (ig, res); loop3 (ig, res)
      end // end of [Some_vt]
    | ~None_vt () => ()
  end // end of [loop3]
  fun loop4 (
      ig: igraph_t, res: &templst
    ) : void = let
    val ans = igraph_search_spill (ig) in
    case+ ans of
    | ~Some_vt tmp => let
        val () = begin
          prerr "igraph_regalloc: loop4(spill): tmp = ";
          $TL.prerr_temp tmp;
          prerr_newline ()
        end // end of [val]
        val () = igraph_node_remove (ig, tmp)
        val () = loop1 (ig, res)
        val () = loop2 (ig, res)
        val () = loop3 (ig, res)
      in
        loop4 (ig, res)
      end // end of [Some_vt]
    | ~None_vt () => ()
  end // end of [loop4]
  var res: templst = list_nil ()
  val () = loop1 (ig, res) // simplify
  val () = loop2 (ig, res) // coalesce
  val () = loop3 (ig, res) // freeze
  val () = loop4 (ig, res) // spill
  val () = begin
    prerr "igraph_regalloc: res = "; $TL.prerr_templst res; prerr_newline ()
  end // end of [val]
in
  res
end // end of [igraph_regalloc]

(* ****** ****** *)

(* end of [regalloc.dats] *)
