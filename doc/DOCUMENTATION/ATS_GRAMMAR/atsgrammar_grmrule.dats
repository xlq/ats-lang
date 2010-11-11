(*
**
** For documenting the grammar of ATS
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Sylvain Nahas (sylvain.nahas AT googlemail DOT com)
**
** Time: November, 2010
**
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "atsgrammar.sats"

(* ****** ****** *)

macdef list_sing (x) = list_cons (,(x), list_nil)

(* ****** ****** *)

typedef _grmrule = '{
  grmrule_kind= int // 0/1 : original/derived
, grmrule_merged= int // 0/1 : available/superceded
, grmrule_symreglst= List (symreg)
} // end of [grmrule]

local

assume grmrule = _grmrule

in // in of [local]

implement
grmrule_make_symlst (xs) = let
  val xs =
    list_map_fun<symbol,symreg> (xs, lam x =<1> SYMREGlit (x))
  // end of [val]
  val xs = list_of_list_vt (xs)
in
  grmrule_make_symreglst (0(*original*), xs)
end // end of [grmrule_make_symlst]

implement
grmrule_make_symreglst (knd, xs) = '{
  grmrule_kind= knd
, grmrule_merged= 0
, grmrule_symreglst= xs
} // end of [grmrule_make_symreglst]

(* ****** ****** *)

implement grmrule_get_kind (gr) = gr.grmrule_kind
implement grmrule_get_merged (gr) = gr.grmrule_merged
implement grmrule_get_symreglst (gr) = gr.grmrule_symreglst

end // end of [local]

(* ****** ****** *)

val theGrmrulelst = ref<grmrulelst_vt> (list_vt_nil)

(* ****** ****** *)

implement
theGrmrulelst_get () = let
  val (vbox pf | p) = ref_get_view_ptr (theGrmrulelst)
  val grs = !p
  val () = !p := list_vt_nil ()
in
  grs
end // end of [theGrmrulelst_get]

(* ****** ****** *)

implement
theGrmrulelst_add (gr) = let
  val (vbox pf | p) = ref_get_view_ptr (theGrmrulelst)
in
  !p := list_vt_cons (gr, !p)
end // end of [theGrmrulelst_add]

(* ****** ****** *)

implement
theGrmrulelst_merge_all
  (x, r) = let
//
  fun loop {n:nat} .<n>.
    (grs: !list_vt (grmrule, n)): void =
    case+ grs of
    | list_vt_cons (gr, !p_grs) => let
        val () = grmrule_set_merged (gr, 1)
        val () = loop (!p_grs)
        val () = fold@ (grs)
      in
        // nothing
      end // end of [val]
    | list_vt_nil () => fold@ (grs)
  // end of [loop]
  val () = let
    val (vbox pf | p) = ref_get_view_ptr (theGrmrulelst)
  in
    $effmask_ref (loop (!p))
  end // end of [val]
//
  val gr = grmrule_make_symreglst (1, list_sing (r))
  val () = theGrmrulelst_add (gr)
in
  // nothing
end // end of [theGrmrulelst_merge]

(* ****** ****** *)

implement
grmrule_append_empty () =
  grmrule_append_symlst (list_nil ())
// end of [grmrule_append_empty]

(* ****** ****** *)

implement
grmrule_append_symbol (x) =
  grmrule_append_symlst (list_sing (x))
// end of [grmrule_append_symbol]

(* ****** ****** *)

implement
grmrule_append_symlst (xs) = let
  val gr = grmrule_make_symlst (xs)
in
  theGrmrulelst_add (gr)
end // end of [grmrule_append_symbol]

(* ****** ****** *)

implement
grmrule_append_grmrule (gr) = theGrmrulelst_add (gr)

(* ****** ****** *)

extern
typedef "atsgrammar_grmrule_t" = _grmrule

%{$
//
ats_void_type
atsgrammar_grmrule_set_kind
  (ats_ptr_type sym, ats_int_type knd) {
  ((atsgrammar_grmrule_t)sym)->atslab_grmrule_kind = knd ;
  return ;
} /* end of [atsgrammar_grmrule_set_kind] */
//
ats_void_type
atsgrammar_grmrule_set_merged
  (ats_ptr_type sym, ats_int_type merged) {
  ((atsgrammar_grmrule_t)sym)->atslab_grmrule_merged = merged ;
  return ;
} /* end of [atsgrammar_grmrule_set_merged] */
//
%} // end of [%{$]

(* ****** ****** *)

(* end of [atsgrammar_grmrule.dats] *)
