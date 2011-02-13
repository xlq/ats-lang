(*
**
** Some utility functions for handling the syntax of ATS
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Guillaume Bruneri (guillaume.bruneri AT gmail DOT com)
**
** Start Time: February, 2011
**
*)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // there is no need for dynloading at run-time
#define ATS_DYNLOADFUN_NAME "atsyntax_initialize"

(* ****** ****** *)

staload Lab = "ats_label.sats"
staload Sym = "ats_symbol.sats"

(* ****** ****** *)

staload "atsyntax_util.sats"

(* ****** ****** *)

implement
tostring_label (l) = let
  val ans = $Lab.label_int_get (l)
in
  case+ ans of
  | ~Some_vt (i) => tostring_int (i)
  | ~None_vt () => let
      val ans = $Lab.label_sym_get (l) in
      case+ ans of
      | ~Some_vt s => $Sym.symbol_name (s) | ~None_vt () => "" (*deadcode*)
    end // end of [None_vt]
end // end of [tostring_label]

(* ****** ****** *)

(* end of [atsyntax_util.dats] *)
