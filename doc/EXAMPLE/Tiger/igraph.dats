(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "tempset.sats"

(* ****** ****** *)

staload F = "frame.sats"

val K = list_length ($F.theGeneralReglst)

(* ****** ****** *)

staload TL = "templab.sats"

(* ****** ****** *)

staload "igraph.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"

(* ****** ****** *)

local

typedef ignodeinfo = '{
  node= $TL.temp_t
, intset= tempset_t, movset= tempset_t
} // end of [ignodeinfo]

assume ignodeinfo_t = ignodeinfo

in // in of [local]

extern typedef "ignodeinfo_t" = ignodeinfo

implement
  ignodeinfo_make (tmp) = let
  val tmps_nil = tempset_nil () in '{
  node= tmp, intset= tmps_nil, movset= tmps_nil
} end // end of [ignodeinfo_make]

implement fprint_ignodeinfo (out, info) = () where {
  val () = fprint_string (out, "node= ")
  val () = $TL.fprint_temp (out, info.node)
  val () = fprint_newline (out)
  val () = fprint_string (out, "intset= ")
  val () = fprint_tempset (out, info.intset)
  val () = fprint_newline (out)
  val () = fprint_string (out, "movset= ")
  val () = fprint_tempset (out, info.movset)
  val () = fprint_newline (out)
} // end of [fprint_ignodeinfo]

implement ignodeinfo_ismove
  (ign) = tempset_isnot_empty (ign.movset)

implement ignodeinfo_intset_get (ign) = ign.intset
implement ignodeinfo_movset_get (ign) = ign.movset

end // end of [local]

implement print_ignodeinfo (info) = fprint_ignodeinfo (stdout_ref, info)
implement prerr_ignodeinfo (info) = fprint_ignodeinfo (stderr_ref, info)

(* ****** ****** *)

staload LM = "LIB/linmap_randbst.dats"
staload _(*anonymous*) = "prelude/DATS/reference.dats"

local

typedef key = $TL.temp_t
typedef itm = ignodeinfo_t
  
assume igraph_t = ref ($LM.map_vt (key, itm)) 

val _cmp_temp = lam (t1: key, t2: key)
  : Sgn =<cloref> $TL.compare_temp_temp (t1, t2)
// end of [_cmp_temp]

in

implement igraph_make_empty () = let
  val map = $LM.linmap_empty {key,itm} () in ref_make_elt (map)
end // end of [igraph_make_empty]

(* ****** ****** *)

implement fprint_igraph (out, ig) = let
  val (vbox pf_ig | p_ig) = ref_get_view_ptr (ig)
  var !p_clo = @lam
    (pf: !unit_v | tmp: key, info: &itm)
    : void =<clo> $effmask_all (let
      val () = fprint_ignodeinfo (out, info)
      val () = fprint_newline (out)
    in
      // empty
    end)
  // end of [var]
  prval pf = unit_v ()
  val () = $LM.linmap_foreach_clo (pf | !p_ig, !p_clo)
  prval unit_v () = pf
in
  // empty
end // end of [fprint_igraph]

(* ****** ****** *)

implement igraph_nodeinfo_get (ig, tmp) = let
  val (vbox pf_ig | p_ig) = ref_get_view_ptr (ig)
  val ans = $LM.linmap_search<key,itm> (!p_ig, tmp, _cmp_temp)
in
  case+ ans of
  | ~Some_vt ign => ign
  | ~None_vt () => ign where {
      val ign = ignodeinfo_make (tmp)
      val ans =
        $LM.linmap_insert<key,itm> (!p_ig, tmp, ign, _cmp_temp)
      // end of [val]
      val () = case+ ans of ~Some_vt _ => () | ~None_vt _ => ()
    } // end of [None_vt]
  // end of [case]
end (* end of [igraph_nodeinfo_get] *)

(* ****** ****** *)

implement igraph_remove_node (ig, tmp) = let
  val ans = let
    val (vbox pf_ig | p_ig) = ref_get_view_ptr (ig)
  in
    $LM.linmap_remove<key,itm> (!p_ig, tmp, _cmp_temp)
  end // end of [val]
in
  case+ ans of
  | ~Some_vt info => let
      val intset = ignodeinfo_intset_get (info)
      val intlst = templst_of_tempset (intset)
      val () = loop (ig, intlst, tmp) where {
        fun loop (
            ig: igraph_t, ts: $TL.templst, t0: $TL.temp_t
          ) : void = case+ ts of
          | list_cons (t, ts) => let
              val () = igraph_int_edge_remove (ig, t, t0)
            in
              loop (ig, ts, t0)
            end // end of [list_cons]
          | list_nil () => ()
        // end of [loop]
      } // end of [val]
      val movset = ignodeinfo_movset_get (info)
      val movlst = templst_of_tempset (movset)
      val () = loop (ig, movlst, tmp) where {
        fun loop (
            ig: igraph_t, ts: $TL.templst, t0: $TL.temp_t
          ) : void = case+ ts of
          | list_cons (t, ts) => let
              val () = igraph_mov_edge_remove (ig, t, t0)
            in
              loop (ig, ts, t0)
            end // end of [list_cons]
          | list_nil () => ()
        // end of [loop]
      } // end of [val]
    in
      // empty
    end // end of [Some_vt]
  | ~None_vt () => ()
end // end of [igraph_remove_node]

(* ****** ****** *)

implement igraph_merge_node (ig, tmp0, tmp1) = let
  val ans = let
    val (vbox pf_ig | p_ig) = ref_get_view_ptr (ig)
  in
    $LM.linmap_remove<key,itm> (!p_ig, tmp1, _cmp_temp)
  end // end of [val]
in
  case+ ans of
  | ~Some_vt info1 => let
      val info0 = igraph_nodeinfo_get (ig, tmp0)
      val () = () where {
        val intset0 = ignodeinfo_intset_get (info0)
        val intset0 = tempset_remove (intset0, tmp1)
        val () = ignodeinfo_intset_set (info0, intset0)
      } // end of [val]
      val () = () where {
        val movset0 = ignodeinfo_movset_get (info0)
        val movset0 = tempset_remove (movset0, tmp1)
        val () = ignodeinfo_movset_set (info0, movset0)
      } // end of [val]
      val intset1 = ignodeinfo_intset_get (info1)
      val intlst1 = templst_of_tempset (intset1)
      val () = loop (ig, tmp0, tmp1, intlst1) where {
        fun loop (
            ig: igraph_t
          , t0: $TL.temp_t, t1: $TL.temp_t
          , ts: $TL.templst
          ) : void = case+ ts of
          | list_cons (t, ts) when
              $TL.eq_temp_temp (t, t0) =>
              loop (ig, t0, t1, ts)
            // end of [list_cons when ...]
          | list_cons (t, ts) => let
              val () = igraph_int_edge_remove (ig, t, t1)
              val info = igraph_nodeinfo_get (ig, t)
              val intset = ignodeinfo_intset_get (info)
              val () = if
                ~tempset_ismem (intset, t0) then
                igraph_int_edge_insert (ig, t, t0)
              // end of [val]]
            in
              loop (ig, t0, t1, ts)
            end // end of [list_cons]
          | list_nil () => ()
        // end of [loop]
      } // end of [val]
      val movset1 = ignodeinfo_movset_get (info1)
      val movlst1 = templst_of_tempset (movset1)
      val () = loop (ig, tmp0, tmp1, movlst1) where {
        fun loop (
            ig: igraph_t
          , t0: $TL.temp_t, t1: $TL.temp_t
          , ts: $TL.templst
          ) : void = case+ ts of
          | list_cons (t, ts) when
              $TL.eq_temp_temp (t, t0) =>
              loop (ig, t0, t1, ts)
            // end of [list_cons when ...]
          | list_cons (t, ts) => let
              val () = igraph_mov_edge_remove (ig, t, t1)
              val info = igraph_nodeinfo_get (ig, t)
              val movset = ignodeinfo_movset_get (info)
              val () = if
                ~tempset_ismem (movset, t0) then
                igraph_mov_edge_insert (ig, t, t0)
              // end of [val]]
            in
              loop (ig, t0, t1, ts)
            end // end of [list_cons]
          | list_nil () => ()
        // end of [loop]
      } // end of [val]
    in
      // empty
    end // end of [Some_vt]
  | ~None_vt () => ()
end // end of [igraph_merge_node]

(* ****** ****** *)

implement igraph_search_lowdeg (ig) = let
  exception Found of $TL.temp_t in try let
    val (vbox pf_ig | p_ig) = ref_get_view_ptr (ig)
    var !p_clo = @lam
      (pf: !unit_v | tmp: key, info: &itm): void =<clo>
      if ignodeinfo_ismove (info) then () else $effmask_all (let
        val intset = ignodeinfo_intset_get (info)
        val size = tempset_size (intset)
      in
        if size < K then $raise (Found tmp) else ()
      end) // end of [if]
    // end of [var]
    prval pf = unit_v ()
    val () = $LM.linmap_foreach_clo (pf | !p_ig, !p_clo)
    prval unit_v () = pf  
  in
    None_vt ()
  end with
    | ~Found tmp => Some_vt (tmp)
  // end of [try]
end // end of [igraph_search_lowdeg]

implement igraph_search_coalesce (ig) = let
  exception Found of ($TL.temp_t, $TL.temp_t)
  fun test (
      ig: igraph_t
    , t0: $TL.temp_t, intset0: tempset_t
    , t1: $TL.temp_t
    ) : bool = ans where {
    val info1 = igraph_nodeinfo_get (ig, t1)
    val intset1 = ignodeinfo_intset_get (info1)
    val intlst1 = templst_of_tempset (intset1)
    val ans = loop (ig, t0, intset0, intlst1) where {
      fun loop (
          ig: igraph_t
        , t0: $TL.temp_t, intset0: tempset_t
        , ts: $TL.templst
        ) : bool = case+ ts of
        | list_cons (t, ts) => begin
          case+ 0 of
          | _ when $TL.eq_temp_temp (t0, t) =>
              loop (ig, t0, intset0, ts)
          | _ when tempset_ismem (intset0, t) =>
              loop (ig, t0, intset0, ts)
          | _ => false (* a more elaborate test is possible *)
          end // end of [list_cons]
        | list_nil () => true // (t0, t1) can be coalesced
      // end of [loop]
    } // end of [val]
  } (* end of [test1] *)
  fun proc (
      ig: igraph_t
    , t0: $TL.temp_t, intset0: tempset_t
    , ts1: $TL.templst
    ) : void = case+ ts1 of
    | list_cons (t1, ts1) => begin
        if test (ig, t0, intset0, t1) then $raise (Found (t0, t1))
        else proc (ig, t0, intset0, ts1)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [proc]
in
  try let
    val (vbox pf_ig | p_ig) = ref_get_view_ptr (ig)
    var !p_clo = @lam
      (pf: !unit_v | tmp: key, info: &itm): void =<clo> let
      val intset = ignodeinfo_intset_get (info)
      val movset = ignodeinfo_movset_get (info)
      val movlst = templst_of_tempset (movset)
    in
      $effmask_all (proc (ig, tmp, intset, movlst))
    end // end of [var]
    prval pf = unit_v ()
    val () = $LM.linmap_foreach_clo (pf | !p_ig, !p_clo)
    prval unit_v () = pf  
  in
    None_vt ()
  end with
    | ~Found (t0, t1) => Some_vt @(t0, t1)
  // end of [try]
end // end of [igraph_search_coalesce]

end // end of [local]

(* ****** ****** *)

implement
  igraph_int_edge_insert (ig, tmp1, tmp2) = let
(*
  val () = prerr "igraph_int_edge_insert:\n"
  val () = (prerr "tmp1 = "; $TL.prerr_temp tmp1; prerr_newline ())
  val () = (prerr "tmp2 = "; $TL.prerr_temp tmp2; prerr_newline ())
*)
  val info1 = igraph_nodeinfo_get (ig, tmp1)
  val info2 = igraph_nodeinfo_get (ig, tmp2)
  val () = () where {
    val intset1 = ignodeinfo_intset_get (info1)
    val intset1 = tempset_add (intset1, tmp2)
    val () = ignodeinfo_intset_set (info1, intset1)
  } // end of [val]
//
  val () = () where {
    val intset2 = ignodeinfo_intset_get (info2)
    val intset2 = tempset_add (intset2, tmp1)
    val () = ignodeinfo_intset_set (info2, intset2)
  } // end of [val]
//
  var flag: int = 0
  val movset1 = ignodeinfo_movset_get (info1)
  val movset1 = tempset_remove_flag (movset1, tmp2, flag)
  val () = if flag > 0 then let
    val () = ignodeinfo_movset_set (info1, movset1)
    val movset2 = ignodeinfo_movset_get (info2)
    val movset2 = tempset_remove_flag (movset2, tmp1, flag)
    val () = ignodeinfo_movset_set (info2, movset2)
  in
    // empty
  end // end of [val]
in
  // empty
end // end of [igraph_int_edge_insert]

implement
  igraph_int_edge_remove (ig, tmp1, tmp2) = let
(*
  val () = prerr "igraph_int_edge_remove:\n"
  val () = (prerr "tmp1 = "; $TL.prerr_temp tmp1; prerr_newline ())
  val () = (prerr "tmp2 = "; $TL.prerr_temp tmp2; prerr_newline ())
*)
  val () = () where {
    val info1 = igraph_nodeinfo_get (ig, tmp1)
    val intset1 = ignodeinfo_intset_get (info1)
    val intset1 = tempset_remove (intset1, tmp2)
    val () = ignodeinfo_intset_set (info1, intset1)
  } // end of [val]
  val () = () where {
    val info2 = igraph_nodeinfo_get (ig, tmp2)
    val intset2 = ignodeinfo_intset_get (info2)
    val intset2 = tempset_remove (intset2, tmp1)
    val () = ignodeinfo_intset_set (info2, intset2)
  } // end of [val]
in
  // empty
end // end of [igraph_int_edge_remove]

(* ****** ****** *)

implement igraph_initialize (ig) = let
  fun loop1 (
      ig: igraph_t, t0: $TL.temp_t, ts: $TL.templst
    ) : void = case+ ts of
    | list_cons (t, ts) => let
        val () = igraph_int_edge_insert (ig, t0, t) in
        loop1 (ig, t0, ts)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop1]
  fun loop2 (
      ig: igraph_t, ts: $TL.templst
    ) : void = case+ ts of
    | list_cons (t, ts) => let
        val () = loop1 (ig, t, ts) in loop2 (ig, ts)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop2]
in
  loop2 (ig, $F.theGeneralReglst)
end // end of [igraph_initialize]

(* ****** ****** *)

implement
  igraph_mov_edge_insert (ig, tmp1, tmp2) = let
  val info1 = igraph_nodeinfo_get (ig, tmp1)
  val intset1 = ignodeinfo_intset_get (info1)
  val isint = tempset_ismem (intset1, tmp2)
in
  if isint then () else let
    val movset1 = ignodeinfo_movset_get (info1)
    val movset1 = tempset_add (movset1, tmp2)
    val () = ignodeinfo_movset_set (info1, movset1)
    val info2 = igraph_nodeinfo_get (ig, tmp2)
    val movset2 = ignodeinfo_movset_get (info2)
    val movset2 = tempset_add (movset2, tmp1)
    val () = ignodeinfo_movset_set (info2, movset2)
  in
    // empty
  end // end of [val]
end // end of [igraph_mov_edge_insert]

implement
  igraph_mov_edge_remove (ig, tmp1, tmp2) = let
  val () = () where {
    val info1 = igraph_nodeinfo_get (ig, tmp1)
    val movset1 = ignodeinfo_movset_get (info1)
    val movset1 = tempset_remove (movset1, tmp2)
    val () = ignodeinfo_movset_set (info1, movset1)
  } // end of [val]
  val () = () where {
    val info2 = igraph_nodeinfo_get (ig, tmp2)
    val movset2 = ignodeinfo_movset_get (info2)
    val movset2 = tempset_remove (movset2, tmp1)
    val () = ignodeinfo_movset_set (info2, movset2)
  } // end of [val]
in
  // empty
end // end of [igraph_mov_edge_remove]

(* ****** ****** *)

%{$

ats_void_type
ignodeinfo_intset_set
  (ats_ptr_type info, ats_ptr_type intset) {
  ((ignodeinfo_t)info)->atslab_intset = intset ; return ;
}

ats_void_type
ignodeinfo_movset_set
  (ats_ptr_type info, ats_ptr_type movset) {
  ((ignodeinfo_t)info)->atslab_movset = movset ; return ;
}

%}

(* ****** ****** *)

(* end of [igraph.dats] *)
