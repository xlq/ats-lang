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
staload "ats_dynexp1_syndef.sats"
macdef matii = match_intlst_intlst

(* ****** ****** *)

staload "atsyndef_util.sats"
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
//
(* ****** ****** *)

val _1_1_1_1_1 = (1 :: 1 :: 1 :: 1 :: 1 :: nil ()): intlst

(* ****** ****** *)

(*
for_list! ($x:$T) `in` $exp1 do $exp2 =>
   let
     var xs: List(T) = $exp1
   in
     while (list_is_cons (xs)) (xs := list_uncons<T> (xs, x); $exp2)
   end
*)

(* ****** ****** *)

extern
fun for_name_1_1_1_1_1 (
  iscons_id: sym_t, uncons_id: sym_t, loc: loc_t, d1es: d1explst
) : d1exp // end of [for_name_1_1_1_1_1]

implement
for_name_1_1_1_1_1 (
  iscons_id, uncons_id, loc0, d1es
) = let
//
  val- cons (d1e5, d1es) = d1es
  val exp2 = d1e5
//
  val- cons (d1e4, d1es) = d1es
  val () = un_d1exp_idext_sym (d1e4, symbol_DO)
//
  val- cons (d1e3, d1es) = d1es
  val exp1 = d1e3
//
  val- cons (d1e2, d1es) = d1es
  val () = un_d1exp_qid_sym (d1e2, symbol_IN)
//
  val- cons (d1e1, d1es) = d1es
  val (x_qid, T) = un_d1exp_ann_type (d1e1)
  val (x_q, x_id) = un_d1exp_qid (x_qid)
//
  val s0taq0 = $Syn.s0taq_none ()
  val d0ynq0 = $Syn.d0ynq_none ()
//
  val x_typ = s1exp_top (T.s1exp_loc, 0(*knd*), T)
  val x_vardec = v1ardec_make 
    (loc0, 0(*non*), x_id, loc0, Some(x_typ), None(*wth*), None(*def*))
  // end of [x_v1ardec]
//
  val xs_id = $Sym.symbol_make_string ("#xs")
  val xs_qid = d1exp_qid (loc0, d0ynq0, xs_id)
//
  val List_id = $Sym.symbol_make_string ("List_forlist")
  val List_qid = s1exp_qid (loc0, s0taq0, List_id)
  val xs_typ = s1exp_app (loc0, List_qid, loc0, T :: nil)
  val xs_vardec = v1ardec_make
    (loc0, 0(*non*), xs_id, loc0, Some(xs_typ), None(*wth*), Some(exp1)(*def*))
  // end of [xs_v1ardec]
  val _let_dec = d1ec_vardecs (loc0, x_vardec :: xs_vardec :: nil)
//
  val _while_inv = loopi1nv_nil (loc0)
//
  val iscons_qid = d1exp_qid (loc0, d0ynq0, iscons_id)
  val _arglst = xs_qid :: nil
  val _while_test = d1exp_app_dyn (loc0, iscons_qid, loc0, 0(*npf*), _arglst)
//
  val _t0id = tmpqi0de_make_qid (loc0, d0ynq0, uncons_id)
  val _decarg = TMPS1EXPLSTLSTcons (T.s1exp_loc, T :: nil, TMPS1EXPLSTLSTnil)
  val uncons_tid = d1exp_tmpid (loc0, _t0id, _decarg)
  val _arglst = xs_qid :: x_qid :: nil
  val uncons_exp = d1exp_app_dyn (loc0, uncons_tid, loc0, 0(*npf*), _arglst)
//
  val _while_body = d1exp_seq (loc0, uncons_exp :: exp2 :: list_nil ())
//
  val _while_loop = d1exp_while (loc0, _while_inv, _while_test, _while_body)
//
in
  d1exp_let (loc0, _let_dec :: nil, _while_loop)
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
  val iscons_id = $Sym.symbol_make_string ("list_is_cons")
  val uncons_id = $Sym.symbol_make_string ("list_uncons_ref")
in
  for_name_1_1_1_1_1 (iscons_id, uncons_id, loc, d1es)
end // end of [forlist_1_1_1_1_1]

(* ****** ****** *)

(* end of [atsyndef_FOR.dats] *)
