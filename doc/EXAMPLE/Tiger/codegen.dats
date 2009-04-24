(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload F = "frame.sats"

(* ****** ****** *)

#include "params.hats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"
staload _(*anonymous*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

#if MARCH == "MIPS" #then

#print "MARCH == MIPS\n"

#include "codegen_mips.dats"

#endif

(* ****** ****** *)

#if MARCH == "x86_32" #then

#print "MARCH == x86_32\n"

#include "codegen_x86_32.dats"

#endif

(* ****** ****** *)

implement codegen_stm (frm, stm) = let
  var res: instrlst_vt = list_vt_nil ()
  val () = instrlst_add_stm (frm, res, stm)
  val res = list_vt_reverse (res)
  val res = list_of_list_vt (res)
in
  res
end // end of [codegen]

implement codegen_stmlst (frm, stms) = let
  var res: instrlst_vt = list_vt_nil ()
  val () = instrlst_add_stmlst (frm, res, stms)
  val res = list_vt_reverse (res)
  val res = list_of_list_vt (res)
in
  res
end // end of [codegen_stmlst]

(* ****** ****** *)

implement codegen_proc (frm, stms) = let
  var res: instrlst_vt = list_vt_nil ()
  val () = $F.procEntryExit1_entr (frm, res)
  val () = instrlst_add_stmlst (frm, res, stms)
  val () = $F.procEntryExit1_exit (frm, res)
  val () = $F.procEntryExit2 (frm, res)
  val res = list_vt_reverse (res)
  val res = list_of_list_vt (res)
in
  res
end // end of [codegen_proc]

(* ****** ****** *)

(* end of [codegen.dats] *)
