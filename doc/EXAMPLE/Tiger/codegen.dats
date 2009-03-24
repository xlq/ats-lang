(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

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
  val () = loop (frm, stms, res) where {
    fun loop (frm: frame, stms: stmlst, res: &instrlst_vt): void =
      case+ stms of
      | list_cons (stm, stms) => let
          val () = instrlst_add_stm (frm, res, stm) in loop (frm, stms, res)
        end // end of [list_cons]
      | list_nil () => ()
    // end of [loop]
  }
  val res = list_vt_reverse (res)
  val res = list_of_list_vt (res)
in
  res
end // end of [codegen]

(* ****** ****** *)

(* end of [codegen.dats] *)
