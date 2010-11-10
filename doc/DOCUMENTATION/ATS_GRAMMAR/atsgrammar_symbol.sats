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

fun symbol_make (name: string): [s:int] symbol(s)

(* ****** ****** *)

fun symbol_set_printname (sym: symbol, pname: string): void

(* ****** ****** *)

fun fprint_symbol (out: FILEref, sym: symbol): void

fun print_symbol (sym: symbol): void
overload print with print_symbol
fun prerr_symbol (sym: symbol): void
overload prerr with prerr_symbol

(* ****** ****** *)

(* end of [atsgrammar_symbol.sats] *)
