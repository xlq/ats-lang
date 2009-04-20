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

implement igraph_remove_node (ig, tmp) = let
  val (vbox pf_ig | p_ig) = ref_get_view_ptr (ig)
  val ans = $LM.linmap_remove<key,itm> (!p_ig, tmp, _cmp_temp)
  val () = (case+ ans of ~Some_vt _ => () | ~None_vt () => ())
  var !p_clo = @lam
    (pf: !unit_v | _: key, info: &itm)
    : void =<clo> $effmask_all (let
      val intset = ignodeinfo_intset_get (info)
      var flag: int = 0
      val intset = tempset_remove_flag (intset, tmp, flag)
    in
      if flag > 0 then ignodeinfo_intset_set (info, intset)
    end)
  // end of [var]
  prval pf = unit_v ()
  val () = $LM.linmap_foreach_clo (pf | !p_ig, !p_clo)
  prval unit_v () = pf  
in
  // empty
end // end of [igraph_remove_node]

implement igraph_search_low (ig) = let
  exception Found of $TL.temp_t in try let
    val (vbox pf_ig | p_ig) = ref_get_view_ptr (ig)
    var !p_clo = @lam
      (pf: !unit_v | tmp: key, info: &itm)
      : void =<clo>
      if ignodeinfo_ismove (info)
        then () else $effmask_all (let
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
end // end of [igraph_search_low]

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
