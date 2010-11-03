(*
**
** Some utility functions for supporting syndef
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** Time: November, 2010
**
*)

(* ****** ****** *)

staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t
staload Sym = "ats_symbol.sats"
typedef sym_t = $Sym.symbol_t

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"

(* ****** ****** *)

typedef intlst = List (int)
fun eq_intlst_intlst (ns1: intlst, ns2: intlst): bool
overload = with eq_intlst_intlst

(* ****** ****** *)

fun fprint_intlst (out: FILEref, ns: intlst): void

(* ****** ****** *)

fun un_d1exp_idext
  (loc: loc_t, d1e: d1exp): sym_t
// end of [un_d1exp_idext]

fun un_d1exp_idext_sym
  (loc: loc_t, d1e: d1exp, id: sym_t): void
// end of [un_d1exp_idext_sym]

(* ****** ****** *)

fun un_d1exp_decseq
  (loc: loc_t, d1e: d1exp): d1eclst
// end of [un_d1exp_decseq]

(* ****** ****** *)

(* end of [atsyndef_util.sats] *)
