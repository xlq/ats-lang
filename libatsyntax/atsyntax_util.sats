(*
**
** Some utility functions for handling the syntax of ATS
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Guillaume Bruneri (guillaume.bruneri AT gmail DOT com)
**
** Time: Start Time, 2011
**
*)

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // there is no need for staloading at run-time

(* ****** ****** *)

staload Lab = "ats_label.sats"

(* ****** ****** *)

fun tostring_label (x: $Lab.label_t): string
overload tostring with tostring_label

(* ****** ****** *)

(* end of [atsyndef_util.sats] *)
