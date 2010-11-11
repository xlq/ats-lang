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

macdef list_sing (x) = list_cons (,(x), list_nil)

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
  | SYMREGopt of (symbol) // [symbol]
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

fun grmrule_make_symlst (xs: symlst): grmrule
fun grmrule_make_symreglst (knd: int, xs: symreglst): grmrule

(* ****** ****** *)

fun grmrule_get_kind (gr: grmrule): int
(*
fun grmrule_set_kind
  (gr: grmrule, knd: int): void = "atsgrammar_grmrule_set_kind"
// end of [grmrule_set_kind]
*)

fun grmrule_get_merged (gr: grmrule): int
fun grmrule_set_merged
  (gr: grmrule, merged: int): void = "atsgrammar_grmrule_set_merged"
// end of [grmrule_set_merged]

fun grmrule_get_symreglst (gr: grmrule): symreglst

(* ****** ****** *)

fun theGrmrulelst_get (): grmrulelst_vt
fun theGrmrulelst_add (x: grmrule): void

fun theGrmrulelst_merge_all (x: symbol, r: symreg): void

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
fun grmrule_append_grmrule (gr: grmrule): void
overload grmrule_append with grmrule_append_grmrule
//
(* ****** ****** *)

fun emit_symdef_yats
  (out: FILEref, x: symbol) : void
// end of [emit_symdef_yats]

fun emit_symdefall_yats (out: FILEref): void

(* ****** ****** *)

fun emit_symdef_desc
  (out: FILEref, x: symbol) : void
// end of [emit_symdef_desc]

fun emit_symdefall_desc (out: FILEref): void

(* ****** ****** *)

(* end of [atsgrammar.sats] *)
