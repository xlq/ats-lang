(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload TL = "templab.sats"

staload TR = "irtree.sats"

(* ****** ****** *)

fun the_labmap_string_insert (lab: $TL.label_t, str: string): void
fun the_labmap_stmlst_insert (lab: $TL.label_t, stms: $TR.stmlst): void

(* ****** ****** *)

fun interp1Prog (stms: $TR.stmlst): void

(* ****** ****** *)

(* end of [interp1.sats] *)
