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

staload "atsgrammar.sats"

(* ****** ****** *)

assume tyname = Stropt

(* ****** ****** *)

implement theTynameNone = stropt_none

(* ****** ****** *)

implement tyname_make_string (x) = let
  val x = string1_of_string (x) in stropt_some (x)
end // end of [tyname_make_string]

(* ****** ****** *)

implement fprint_tyname (out, x) =
  if stropt_is_some (x) then let
    val x = stropt_unsome (x) in fprint_string (out, x)
  end else ()
// end of [fprint_tyname]

implement print_tyname (x) = fprint_tyname (stdout_ref, x)
implement prerr_tyname (x) = fprint_tyname (stderr_ref, x)

(* ****** ****** *)

implement tyname_is_some (x) = stropt_is_some (x)

(* ****** ****** *)

(* end of [atsgrammar_tyname.dats] *)
