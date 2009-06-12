(*
** some testing code for functions declared in
** libats/smlbas/SATS/array.sats
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Summer, 2009
//

(* ****** ****** *)

staload "libats/smlbas/SATS/char.sats"

(* ****** ****** *)

dynload "libats/smlbas/DATS/char.dats"

(* ****** ****** *)

implement main () = () where {
  val () = printf ("toCString '\\n' = %s\n", @(toCString '\n'))
  val () = printf ("toCString '\\101' = %s\n", @(toCString '\101'))
  val () = printf ("toCString '\\177' = %s\n", @(toCString '\177'))
} // end of [main]

(* ****** ****** *)

(* end of [libats_smlbas_array.dats] *)
