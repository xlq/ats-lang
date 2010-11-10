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

staload "atsgrammar_symbol.sats"
staload "atsgrammar_grmrule.sats"

(* ****** ****** *)

absview symbol_open_v (s:int)

fun symbol_open {s:int}
  (sym: symbol (s)): (symbol_open_v (s) | void)
// end of [symbol_open]

fun symbol_close {s:int}
  (pf: symbol_open_v (s) | sym: symbol (s)): void
// end of [symbol_clsoe]

(* ****** ****** *)

symintr grmrule_append
//
fun grmrule_append_empty (): void
overload grmrule_append with grmrule_append_empty
//
fun grmrule_append_symbol (x: symbol): void
overload grmrule_append with grmrule_append_symbol
//
fun grmrule_append_symlst (xs: symlst): void
overload grmrule_append with grmrule_append_symlst

(* ****** ****** *)

(* end of [atsgrammar_main.sats] *)
