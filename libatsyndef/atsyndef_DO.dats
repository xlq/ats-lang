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

(* ****** ****** *)

val _1_1_1 = (1 :: 1 :: 1 :: nil ()): intlst

(* ****** ****** *)

(*
do! ($exp1) `while` ($exp2) =>
  while (true)
    let #declst($exp1) in if ($exp2) then continue else break end
  // end of [while]
*)

extern
fun do_1_1_1 (loc: loc_t, d1es: d1explst): d1exp

implement
do_search (ns) = let
(*
  val () = print "do_search: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when ns \matii _1_1_1 => Some_vt (do_1_1_1)
  | _ => None_vt ()
end // end of [do_search]

(* ****** ****** *)

implement
do_1_1_1 (loc0, d1es) = let
//
  val- cons (d1e3, d1es) = d1es
//
  val- cons (d1e2, d1es) = d1es
  val () = un_d1exp_qid_sym (d1e2, symbol_WHILE)
//
  val- cons (d1e1, d1es) = d1es
  val d1cs1 = un_d1exp_decseq (d1e1)
//
  val _cond = d1e3
  val _then = d1exp_loopexn (loc0, 1) // continue
  val _else = Some (d1exp_loopexn (loc0, 0)) // break
  val _if = d1exp_if (loc0, i1nvresstate_nil, _cond, _then, _else)
//
  val _inv = loopi1nv_nil (loc0)
  val _test = d1exp_bool (loc0, true)
  val _let = d1exp_let (loc0, d1cs1, _if)
//
in
  d1exp_while (loc0, _inv, _test, _let)
end // end of [do_1_1_1]

(* ****** ****** *)

(* end of [atsyndef_main.dats] *)
