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

(* ****** ****** *)

assume
symbol (s:int) = '{
  symbol_name= string
, symbol_printname= Stropt
, symbol_stamp= int
} // end of [symbol]

(* ****** ****** *)

implement
symbol_make
  (name) = #[0 | '{
  symbol_name= name
, symbol_printname= stropt_none
, symbol_stamp= 0
} ] // end of [symbol_make]

(* ****** ****** *)

implement
fprint_symbol
  (out, sym) = let
  val () = fprint (out, sym.symbol_name)
  val () = fprint (out, "(")
  val () = fprint (out, sym.symbol_stamp)
  val () = fprint (out, ")")
in
  // nothing
end // end of [fprint_symbol]

implement print_symbol (sym) = fprint_symbol (stdout_ref, sym)
implement prerr_symbol (sym) = fprint_symbol (stderr_ref, sym)

(* ****** ****** *)

(* end of [atsgrammar_symbol.sats] *)
