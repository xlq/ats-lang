(*
**
** A simple Clutter example: a window
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: June, 2010
**
*)

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%} // end of [%{^]

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"

(* ****** ****** *)

staload "contrib/Clutter/SATS/clutter.sats"
staload "contrib/Clutter/SATS/clutterclassdec.sats"

(* ****** ****** *)

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val (fpf_stage | stage) = clutter_stage_get_default ()
//
  var color: ClutterColor
  val () = color.red := (guint8)0U
  val () = color.green := (guint8)0U
  val () = color.blue := (guint8)0U
  val () = color.alpha := (guint8)0xFFU
  val () = clutter_stage_set_color (stage, color)
//
  val () = clutter_actor_set_size (stage, (gfloat)512.0, (gfloat)512.0)
//
  val () = clutter_actor_show (stage)
  val () = clutter_main ()
//
  prval () = fpf_stage (stage)
} // end of [main1]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$
ats_void_type
mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  clutter_init ((int*)&argc, (char***)&argv) ; main1 () ; return ;
} // end of [mainats]
%} // end of [%{$]

(* ****** ****** *)

(* end of [clutter-test01.dats] *)
