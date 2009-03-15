(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload FRM = "frame.sats"
staload TR = "irtree.sats"
staload ASM = "assembly.sats"

fun codegen (frm: $FRM.frame_t, stm: $TR.stm): $ASM.instrlst

(* ****** ****** *)

(* end of [codegen.sats] *)
