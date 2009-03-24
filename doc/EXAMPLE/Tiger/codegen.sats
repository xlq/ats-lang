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
staload ASM = "assem.sats"

fun codegen_stm (frm: $FRM.frame_t, stm: $TR.stm): $ASM.instrlst
fun codegen_stmlst (frm: $FRM.frame_t, stms: $TR.stmlst): $ASM.instrlst

(* ****** ****** *)

(* end of [codegen.sats] *)
