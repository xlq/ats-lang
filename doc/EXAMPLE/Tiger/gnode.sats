(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

abst@ype gnode_t = $extype "ats_int_type"

abstype gnodelst_t // this list is assumed to be ordered

(* ****** ****** *)

castfn int_of_gnode (_: gnode_t): Nat
castfn gnode_of_int (_: Nat): gnode_t

(* ****** ****** *)

fun gnode_make_int (n: Nat): gnode_t

(* ****** ****** *)

fun fprint_gnode (out: FILEref, gn: gnode_t): void
fun print_gnode (gn: gnode_t): void
fun prerr_gnode (gn: gnode_t): void

(* ****** ****** *)

fun fprint_gnodelst (out: FILEref, gns: gnodelst_t): void
fun print_gnodelst (gns: gnodelst_t): void
fun prerr_gnodelst (gns: gnodelst_t): void

(* ****** ****** *)

fun eq_gnode_gnode (gn1: gnode_t, gn2: gnode_t):<> bool
overload = with eq_gnode_gnode

fun compare_gnode_gnode (gn1: gnode_t, gn2: gnode_t):<> Sgn
overload compare with compare_gnode_gnode

(* ****** ****** *)

fun gnodelst_nil (): gnodelst_t
fun gnodelst_sing (gn: gnode_t): gnodelst_t

(* ****** ****** *)

fun gnodelst_ismem (gns: gnodelst_t, gn: gnode_t): bool

(* ****** ****** *)

fun gnodelst_add
  (gns: gnodelst_t, gn: gnode_t): gnodelst_t

fun gnodelst_add_flag
  (gns: gnodelst_t, gn: gnode_t, flag: &int): gnodelst_t

(* ****** ****** *)

fun gnodelst_union
  (gns1: gnodelst_t, gns2: gnodelst_t): gnodelst_t

fun gnodelst_union_flag
  (gns1: gnodelst_t, gns2: gnodelst_t, flag: &int): gnodelst_t

(* ****** ****** *)

(* end of [gnode.sats] *)
