(*
**
** Some utility functions for supporting syndef
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: November, 2010
**
*)

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t
staload Sym = "ats_symbol.sats"
typedef sym_t = $Sym.symbol_t
overload = with $Sym.eq_symbol_symbol

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"

(* ****** ****** *)

staload "atsyndef_util.sats"
macdef matii = match_intlst_intlst

(* ****** ****** *)

staload "atsyndef_main.sats"

(* ****** ****** *)

#define nil list_nil
#define :: list_cons
#define cons list_cons

(* ****** ****** *)
//
val symbol_IN = $Sym.symbol_IN
val symbol_WHILE = $Sym.symbol_WHILE
//
val symbol_DO = $Sym.symbol_make_string "do"
val symbol_FORLIST = $Sym.symbol_make_string "for_list"

(* ****** ****** *)

val _1_1_1_1_1 = (1 :: 1 :: 1 :: 1 :: 1 :: nil ()): intlst

(* ****** ****** *)

(*
`for_list` ($x:$T) `in` $xs `do` $exp =>
  forlist_in_do<$T> ($xs, lam ($x) => $exp)
*)

extern
fun for_name_1_1_1_1_1
  (name: sym_t, loc: loc_t, d1es: d1explst): d1exp
// end of [for_name_1_1_1_1_1]

implement
for_name_1_1_1_1_1
  (fid, loc0, d1es) = let
//
  val- cons (d1e5, d1es) = d1es
  val _exp = d1e5
//
  val- cons (d1e4, d1es) = d1es
  val () = un_d1exp_qid_sym (d1e4, symbol_DO)
//
  val- cons (d1e3, d1es) = d1es
  val _xs = d1e3
//
  val- cons (d1e2, d1es) = d1es
  val () = un_d1exp_qid_sym (d1e2, symbol_IN)
//
  val- cons (d1e1, d1es) = d1es
  val (_qid, _typ) = un_d1exp_ann_type (d1e1)
  val (_q, _id) = un_d1exp_qid (_qid)
//
  val loc1 = d1e1.d1exp_loc
  val _x = p1at_qid (loc1, _q, _id)
  val _lam = d1exp_lam_dyn (_exp.d1exp_loc, 0(*lin*), _x, _exp)
//
  val q = $Syn.d0ynq_none ()
  val _t0id = tmpqi0de_make_qid (loc0, q, fid)
//
  val _decarg = TMPS1EXPLSTLSTcons
    (_typ.s1exp_loc, _typ :: nil, TMPS1EXPLSTLSTnil)
  val _t1id = d1exp_tmpid (loc0, _t0id, _decarg)
  val _arglst = _xs :: _lam :: list_nil ()
  val loc_arg = $Loc.location_combine (_xs.d1exp_loc, _lam.d1exp_loc)
in
  d1exp_app_dyn (loc0, _t1id, loc_arg, 0(*npf*), _arglst)
end // end of [for_name_1_1_1_1_1]

(* ****** ****** *)

extern
fun forlist_1_1_1_1_1
  (loc: loc_t, d1es: d1explst): d1exp
// end of [forlist_1_1_1_1_1]

implement
forlist_search (ns) = let
(*
  val () = print "forlist_search: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when ns \matii _1_1_1_1_1 => Some_vt (forlist_1_1_1_1_1)
  | _ => None_vt ()
end // end of [forlist_search]

implement
forlist_1_1_1_1_1
  (loc, d1es) = let
  val name =
    $Sym.symbol_make_string ("forlist_in_do")
in
  for_name_1_1_1_1_1 (name, loc, d1es)
end // end of [forlist_1_1_1_1_1]

(* ****** ****** *)

(* end of [atsyndef_FOR.dats] *)
