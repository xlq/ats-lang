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
viewtypedef symlst_vt = List_vt (symbol)

(* ****** ****** *)

datatype symreg =
  | SYMREGlit of symbol // symbol
  | SYMREGseq of (symbol, symbol) // (symbol , symbol)
  | SYMREGalt of (symbol, symbol) // (symbol | symbol)
  | SYMREGstar of (symbol) // {symbol}
  | SYMREGplus of (symbol) // {symbol}+
// end of [symreg]

typedef symreglst = List (symreg)

(* ****** ****** *)

abstype grmrule
typedef grmrulelst = List (grmrule)
viewtypedef grmrulelst_vt = List_vt (grmrule)

(* ****** ****** *)

fun symbol_make (name: string): symbol
fun symbol_make_nt (name: string): symbol

(* ****** ****** *)

fun eq_symbol_symbol
  (x1: symbol, x2: symbol): bool
overload = with eq_symbol_symbol

fun symbol_get_name (x: symbol): string

fun symbol_get_nonterm (x: symbol): bool
fun symbol_set_nonterm (
  x: symbol, nt: bool
) :<!ref> void = "atsgrammar_symbol_set_nonterm"
// end of [symbol_set_nonterm]

fun symbol_get_fullname (x: symbol): Stropt
fun symbol_set_fullname (
  x: symbol, fname: string
) :<!ref> void = "atsgrammar_symbol_set_fullname"
// end of [symbol_set_fullname]

fun symbol_get_grmrulelst (x: symbol): grmrulelst
fun symbol_set_grmrulelst (
  x: symbol, grs: grmrulelst
) :<!ref> void = "atsgrammar_symbol_set_grmrulelst"
// end of [symbol_set_grmrulelst]

(* ****** ****** *)

fun fprint_symbol (out: FILEref, sym: symbol): void

fun print_symbol (sym: symbol): void
overload print with print_symbol
fun prerr_symbol (sym: symbol): void
overload prerr with prerr_symbol

(* ****** ****** *)

fun theSymlst_get (): symlst
fun theSymlst_add (x: symbol): void

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

fun emit_symdef_yats
  (out: FILEref, x: symbol) : void
// end of [emit_symdef_yats]

fun emit_symdefall_yats (out: FILEref): void

(* ****** ****** *)

(* end of [atsgrammar.sats] *)
