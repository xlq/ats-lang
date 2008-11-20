(*
**
** HOLIMUS: a proof checker
**
** Originally implemented in OCaml
**    by Chad Brown (cebrown AT mathgate DOT info)
**
** Translated to ATS
**    by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
*)

(* ****** ****** *)

datatype stp =
  | STPbas of string
  | STPprp of ()
  | STParr of (stp, stp)

fun print_stp (x: stp): void
fun prerr_stp (x: stp): void

(* ****** ****** *)

datatype trm =
  | TRMnam of string
  | TRMdbi of int
  | TRMlam of (stp, trm)
  | TRMapp of (trm, trm)
  | TRMall of (stp, trm)
  | TRMimp of (trm, trm)
  | TRMany of stp

fun print_trm (x: trm): void
fun prerr_trm (x: trm): void

(* ****** ****** *)

datatype pftrm =
  | PFTRMcon of string
  | PFTRMdbi of int
  | PFTRMtlam of (stp, pftrm)
  | PFTRMplam of (trm, pftrm)
  | PFTRMtapp of (pftrm, trm)
  | PFTRMpapp of (pftrm, pftrm)
  | PFTRMksi of pftrm

fun print_pftrm (x: pftrm): void
fun prerr_pftrm (x: pftrm): void

(* ****** ****** *)

fun prop_false (): trm and prop_true (): trm

fun eq_stp_stp (_: stp, _: stp): bool
overload = with eq_stp_stp

fun eq_trm_trm (_: trm, _: trm): bool
overload = with eq_trm_trm

(* ****** ****** *)

(* end of [syntax.sats] *)
