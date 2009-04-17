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

(* ****** ****** *)

abstype gtempset_t

(* ****** ****** *)

fun gtempset_nil (): gtempset_t

(* ****** ****** *)

fun gtempset_ismem (gts: gtempset_t, t: $TL.temp_t): bool

(* ****** ****** *)

fun gtempset_add
  (gts: gtempset_t, t: $TL.temp_t): gtempset_t

fun gtempset_add_flag
  (gts: gtempset_t, t: $TL.temp_t, flag: &int): gtempset_t

(* ****** ****** *)

fun gtempset_union
  (gts1: gtempset_t, gts2: gtempset_t): gtempset_t

fun gtempset_union_flag
  (gts1: gtempset_t, gts2: gtempset_t, flag: &int): gtempset_t

(* ****** ****** *)

(* end of [gtemp.sats] *)
