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

abstype symbol (s:int)
typedef symbol = [s:int] symbol (s)
typedef symlst = List (symbol)

(* ****** ****** *)

abstype grmrule
typedef grmrulelst = List (grmrule)
viewtypedef grmrulelst_vt = List_vt (grmrule)

(* ****** ****** *)

fun symbol_make (name: string): [s:int] symbol(s)
//
fun symbol_get_printname (x: symbol): Stropt
fun symbol_set_printname (x: symbol, pname: string): void
//
fun symbol_get_grmrulelst (x: symbol): grmrulelst
fun symbol_set_grmrulelst (x: symbol, grs: grmrulelst): void

(* ****** ****** *)

fun fprint_symbol (out: FILEref, sym: symbol): void

fun print_symbol (sym: symbol): void
overload print with print_symbol
fun prerr_symbol (sym: symbol): void
overload prerr with prerr_symbol

(* ****** ****** *)

fun theGrmrulelst_get (): grmrulelst_vt
fun theGrmrulelst_add (x: grmrule): void

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
//
(* ****** ****** *)

(* end of [atsgrammar.sats] *)
