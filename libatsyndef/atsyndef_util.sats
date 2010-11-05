(*
**
** Some utility functions for supporting syndef
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: November, 2010
**
*)

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // there is no need for staloading at run-time

(* ****** ****** *)

staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t
staload Sym = "ats_symbol.sats"
typedef sym_t = $Sym.symbol_t
staload Syn = "ats_syntax.sats"
typedef tmpqi0de = $Syn.tmpqi0de

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"

(* ****** ****** *)

typedef intlst = List (int)
fun match_intlst_intlst (ns1: intlst, ns2: intlst): bool

(* ****** ****** *)

fun tmpqi0de_make_qid
  (loc: loc_t, q: d0ynq, id: sym_t): tmpqi0de
// end of [tmpqi0de_make_qid]

(* ****** ****** *)

fun un_d1exp_ann_type (d1e: d1exp): (d1exp, s1exp)

(* ****** ****** *)

fun un_d1exp_qid (d1e: d1exp): (d0ynq, sym_t)
fun un_d1exp_qid_sym (d1e: d1exp, id: sym_t): void

(* ****** ****** *)

fun un_d1exp_idext (d1e: d1exp): sym_t
fun un_d1exp_idext_sym (d1e: d1exp, id: sym_t): void

(* ****** ****** *)

fun un_d1exp_decseq (d1e: d1exp): d1eclst

(* ****** ****** *)

(* end of [atsyndef_util.sats] *)
