(*
**
** Some utility functions for supporting syndef
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: November, 2010
**
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"

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

macdef list_sing (x) = list_cons (,(x), list_nil)

(* ****** ****** *)
//
val symbol_IN = $Sym.symbol_IN
val symbol_WHILE = $Sym.symbol_WHILE
//
val symbol_DO = $Sym.symbol_make_string "do"
val symbol_FORLIST = $Sym.symbol_make_string "for_list"

(* ****** ****** *)

val _neg1 = (~1 :: nil ()): intlst

(* ****** ****** *)

extern
fun print_neg1
  (loc: loc_t, d1es: d1explst): d1exp
// end of [print_neg1]

extern
fun println_neg1
  (loc: loc_t, d1es: d1explst): d1exp
// end of [print_neg1]

(* ****** ****** *)

implement
print_search (ns) = let
(*
  val () = print "print_search: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when ns \matii _neg1 => Some_vt (print_neg1)
  | _ => None_vt ()
end // end of [print_search]

implement
println_search (ns) = let
(*
  val () = print "println_search: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when ns \matii _neg1 => Some_vt (println_neg1)
  | _ => None_vt ()
end // end of [println_search]

(* ****** ****** *)

implement
print_neg1 (loc0, d1es) = let
//
  val q = $Syn.d0ynq_none ()
  val id = $Sym.symbol_make_string ("print")
  val _print = d1exp_qid (loc0, q, id)
//
  val- cons (d1e, _) = d1es
//
in
  case+ d1e.d1exp_node of
  | D1Elist (_(*npf*), d1es) => let
      fun f (
        pf: !unit_v | d1e: d1exp
      ) :<cloptr1> d1exp = let
        val loc = d1e.d1exp_loc in
        d1exp_app_dyn (loc, _print, loc, 0(*npf*), list_sing (d1e))
      end // end of [f]
      prval pfu = unit_v ()
      val d1es = list_map_cloptr {unit_v} (pfu | d1es, f)
      prval unit_v () = pfu
      val d1es = list_of_list_vt (d1es)
    in
      d1exp_seq (loc0, d1es)
    end // end of [D1Elist]
  | _ => let
      val loc = d1e.d1exp_loc in
      d1exp_app_dyn (loc, _print, loc, 0(*npf*), list_sing (d1e))
    end // end of [_]
end // end of [print_neg1]

(* ****** ****** *)

implement
println_neg1 (loc0, d1es) = let
  val d1e1 = print_neg1 (loc0, d1es)
//
  val q = $Syn.d0ynq_none ()
  val id = $Sym.symbol_make_string ("println")
  val _println = d1exp_qid (loc0, q, id)
//
  val d1e2 = d1exp_app_dyn (loc0, _println, loc0, 0(*npf*), list_nil)
in
  d1exp_seq (loc0, d1e1 :: d1e2 :: list_nil)
end // end of [println_neg1]

(* ****** ****** *)

(* end of [atsyndef_PRINT.dats] *)
