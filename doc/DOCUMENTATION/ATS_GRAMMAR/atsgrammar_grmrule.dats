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

staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "atsgrammar.sats"

(* ****** ****** *)

macdef list_sing (x) = list_cons (,(x), list_nil)

(* ****** ****** *)

extern
fun grmrule_make_symlst (xs: symlst): grmrule

local

assume grmrule = List (symbol)

in // in of [local]

implement grmrule_make_symlst (xs) = xs

end // end of [local]

(* ****** ****** *)

val theGrmrulelst = ref<grmrulelst_vt> (list_vt_nil)

(* ****** ****** *)

implement
theGrmrulelst_get () = let
  val (vbox pf | p) = ref_get_view_ptr (theGrmrulelst)
  val xs = !p
  val () = !p := list_vt_nil ()
in
  xs
end // end of [theGrmrulelst_get]

(* ****** ****** *)

implement
theGrmrulelst_add (x) = let
  val (vbox pf | p) = ref_get_view_ptr (theGrmrulelst)
in
  !p := list_vt_cons (x, !p)
end // end of [theGrmrulelst_add]

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

(* end of [atsgrammar_grmrule.dats] *)
