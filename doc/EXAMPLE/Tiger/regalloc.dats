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

staload "tempset.sats"

(* ****** ****** *)

staload "igraph.sats"

(* ****** ****** *)

staload "regalloc.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"
staload _(*anonymous*) = "prelude/DATS/reference.dats"

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

implement fprint_regassgn (out, rasgn) = begin
  case+ rasgn of
  | REGASSGNsimplify (tmp, intset) => () where {
      val () = fprint_string (out, "REGASSGNsimplify(")
      val () = $TL.fprint_temp (out, tmp)
      val () = fprint_string (out, "; ")
      val () = fprint_tempset (out, intset)
      val () = fprint_string (out, ")")
    } // end of [REGASSGNsimplify]
  | REGASSGNcoalesce (tmp0, tmp1) => () where {
      val () = fprint_string (out, "REGASSGNcoalesce(")
      val () = $TL.fprint_temp (out, tmp0)
      val () = fprint_string (out, "; ")
      val () = $TL.fprint_temp (out, tmp1)
      val () = fprint_string (out, ")")
    } // end of [REGASSGNcoalesce]
  | REGASSGNspill (tmp, intset) => () where {
      val () = fprint_string (out, "REGASSGNspill(")
      val () = $TL.fprint_temp (out, tmp)
      val () = fprint_string (out, "; ")
      val () = fprint_tempset (out, intset)
      val () = fprint_string (out, ")")
    } // end of [REGASSGNspill]
end // end of [fprint_regassgn]

(* ****** ****** *)

implement fprint_regassgnlst (out, rasgns) =
  case+ rasgns of
  | list_cons (rasgn, rasgns) => let
      val () = fprint_regassgn (out, rasgn)
      val () = fprint_newline (out)
    in
      fprint_regassgnlst (out, rasgns)
    end // end of [list_cons]
  | list_nil () => ()
// end of [fprint_regassgnlst]

(* ****** ****** *)

val theGeneralRegset : tempset_t =
  tempset_make_templst ($F.theGeneralReglst)

(* ****** ****** *)

local

staload LM = "LIB/linmap_randbst.dats"

typedef key = $TL.temp_t
typedef itm = $TL.temp_t
  
typedef regassgnmap = ref ($LM.map_vt (key, itm))

val _cmp_temp = lam (t1: key, t2: key)
  : Sgn =<cloref> $TL.compare_temp_temp (t1, t2)
// end of [_cmp_temp]

val theRegAssgnMap = let
  val map = $LM.linmap_empty {key,itm} () in ref_make_elt (map)
end : regassgnmap // end of [val]

in // in of [local]

fn regassgn_find (tmp: $TL.temp_t): $TL.tempopt_vt = let
  val (vbox pf | p) = ref_get_view_ptr (theRegAssgnMap) in
  $LM.linmap_search<key,itm> (!p, tmp, _cmp_temp)
end (* end of [regassgn_find] *)

fn regassgn_insert
  (tmp0: $TL.temp_t, tmp1: $TL.temp_t): void = let
  val (vbox pf | p) = ref_get_view_ptr (theRegAssgnMap)
  val ans = $LM.linmap_insert<key,itm> (!p, tmp0, tmp1, _cmp_temp)
  val () = case+ ans of ~Some_vt _ => () | ~None_vt () => ()
in
  // empty
end (* end of [regassgn_insert] *)

end // end of [local]

(* ****** ****** *)

implement regassgn_select (rasgn) = let
  fun auxsel
    (rems: tempset_t, ts: $TL.templst): $TL.tempopt_vt =
    case+ ts of
    | list_cons (t, ts) => let
        val t = begin
          case+ regassgn_find (t) of ~Some_vt t => t | ~None_vt () => t
        end // end of [val]
        val rems = tempset_remove (rems, t) in auxsel (rems, ts)
      end (* end of [list_cons] *)
    | list_nil () => let
        val rems = templst_of_tempset (rems) in case+ rems of
        | list_cons (t, _) => Some_vt t | list_nil () => None_vt ()
      end // end of [list_nil]
  // end of [auxsel]
  var tmp0: $TL.temp_t = $TL.temp_bogus
  val ans = (case+ rasgn of
    | REGASSGNsimplify (t0, ts) => let
        val () = tmp0 := t0
        val ts = templst_of_tempset ts in auxsel (theGeneralRegset, ts)
      end // end of [REGASSGNsimplify]
    | REGASSGNcoalesce (t0, t1) => let
        val () = tmp0 := t1
        val t0 = begin
          case+ regassgn_find (t0) of ~Some_vt t => t | ~None_vt () => t0
        end // end of [val]
      in
        Some_vt t0
      end // end of [REGASSGNcoalesce]
    | REGASSGNspill (t0, ts) => let
        val () = prerr "regassgn_select: potential spill\n"
        val () = tmp0 := t0
        val ts = templst_of_tempset ts in auxsel (theGeneralRegset, ts)
      end // end of [REGASSGNspill]
  ) : $TL.tempopt_vt
  val () = case+ ans of
    | ~Some_vt tmp1 => let
        val () = regassgn_insert (tmp0, tmp1)
      in
        prerr "regassgn_select: ";
        $TL.prerr_temp tmp0; prerr " --> "; $TL.prerr_temp tmp1;
        prerr_newline ()
      end // end of [Some_vt]
    | ~None_vt () => let
        val () = ()
      in
        prerr "regassgn_select: ";
        $TL.prerr_temp tmp0; prerr " --> (spill)";
        prerr_newline ()
      end // end of [None_vt]
in
  // empty        
end // end of [regassgn_select]

(* ****** ****** *)

implement igraph_regalloc (ig) = let
  fun loop1 (
      ig: igraph_t, rasgns: &regassgnlst
    ) : void = let
    val ans = igraph_search_lowdeg (ig) in
    case+ ans of
    | ~Some_vt tmp => let
        val () = begin
          prerr "igraph_regalloc: loop1(simplify): tmp = ";
          $TL.prerr_temp tmp;
          prerr_newline ()
        end // end of [val]
        val info = igraph_nodeinfo_get (ig, tmp)
        val intset = ignodeinfo_intset_get (info)
        val rasgn = REGASSGNsimplify (tmp, intset)
        val () = rasgns := list_cons (rasgn, rasgns)
        val () = igraph_node_remove (ig, tmp)
      in
        loop1 (ig, rasgns)
      end // end of [Some_vt]
    | ~None_vt () => ()
  end // end of [loop1]
  fun loop2 (
      ig: igraph_t, rasgns: &regassgnlst
    ) : void = let
    val ans = igraph_search_coalesce (ig) in
    case+ ans of
    | ~Some_vt tmptmp => let
        val tmp0 = tmptmp.0 and tmp1 = tmptmp.1
// (*
        val () = begin
          prerr "igraph_regalloc: loop2(coalesce): ";
          $TL.prerr_temp tmp0;
          prerr " <=> ";
          $TL.prerr_temp tmp1;
          prerr_newline ()
        end // end of [val]
// *)
        val rasgn = REGASSGNcoalesce (tmp0, tmp1)
        val () = rasgns := list_cons (rasgn, rasgns)
        val () = igraph_node_coalesce (ig, tmp0, tmp1)
      in
        loop1 (ig, rasgns); loop2 (ig, rasgns)
      end // end of [Some_vt]
    | ~None_vt () => ()
  end // end of [loop2]
  fun loop3 (
      ig: igraph_t, rasgns: &regassgnlst
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
        val () = loop1 (ig, rasgns)
        val () = loop2 (ig, rasgns)
        val () = loop3 (ig, rasgns)
      in
        // empty
      end // end of [Some_vt]
    | ~None_vt () => ()
  end // end of [loop3]
  fun loop4 (
      ig: igraph_t, rasgns: &regassgnlst
    ) : void = let
    val ans = igraph_search_spill (ig) in
    case+ ans of
    | ~Some_vt tmp => let
        val () = begin
          prerr "igraph_regalloc: loop4(spill): tmp = ";
          $TL.prerr_temp tmp;
          prerr_newline ()
        end // end of [val]
        val info = igraph_nodeinfo_get (ig, tmp)
        val intset = ignodeinfo_intset_get (info)
        val rasgn = REGASSGNspill (tmp, intset)
        val () = rasgns := list_cons (rasgn, rasgns)
        val () = igraph_node_remove (ig, tmp)
        val () = loop1 (ig, rasgns)
        val () = loop2 (ig, rasgns)
        val () = loop3 (ig, rasgns)
        val () = loop4 (ig, rasgns)
      in
        // empty
      end // end of [Some_vt]
    | ~None_vt () => ()
  end // end of [loop4]
  var rasgns: regassgnlst = list_nil ()
  val () = loop1 (ig, rasgns) // simplify
  val () = loop2 (ig, rasgns) // coalesce
  val () = loop3 (ig, rasgns) // freeze
  val () = loop4 (ig, rasgns) // spill
  val () = begin
    prerr "igraph_regalloc: rasgns =\n";
    fprint_regassgnlst (stderr_ref, rasgns);
    prerr_newline ()
  end // end of [val]
  val () = loop5 (rasgns) where {
    fun loop5 (rasgns: regassgnlst): void =
      case+ rasgns of
      | list_cons (rasgn, rasgns) => let
          val () = regassgn_select (rasgn) in loop5 (rasgns)
        end // end of [list_cons]
      | list_nil () => ()
    // end of [loop5]
  }
in
  rasgns
end // end of [igraph_regalloc]

(* ****** ****** *)

(* end of [regalloc.dats] *)
