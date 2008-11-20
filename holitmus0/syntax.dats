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

staload "syntax.sats"

(* ****** ****** *)

val _0 = TRMdbi 0

implement prop_false () = TRMall (STPprp (), _0)
implement prop_true () = TRMall (STPprp (), TRMimp (_0, _0))

(* ****** ****** *)

implement eq_stp_stp (x1, x2) = eq (x1, x2) where {
  fun eq (x1: stp, x2: stp): bool =
    case+ (x1, x2) of
    | (STPbas nam1, STPbas nam2) => (nam1 = nam2)
    | (STPprp (), STPprp ()) => true
    | (STParr (x11, x12), STParr (x21, x22)) =>
        if eq (x11, x21) then eq (x12, x22) else false
    | (_, _) => false
} // end of [eq_stp_stp]

(* ****** ****** *)

implement eq_trm_trm (x1, x2) = eq (x1, x2) where {
  fun eq (x1: trm, x2: trm): bool =
    case+ (x1, x2) of
    | (TRMnam nam1, TRMnam nam2) => (nam1 = nam2)
    | (TRMdbi ind1, TRMdbi ind2) => (ind1 = ind2)
    | (TRMlam (stp1, trm1), TRMlam (stp2, trm2)) =>
        if stp1 = stp2 then eq (trm1, trm2) else false
    | (TRMall (stp1, trm1), TRMall (stp2, trm2)) =>
        if stp1 = stp2 then eq (trm1, trm2) else false
    | (TRMimp (trm11, trm12), TRMimp (trm21, trm22)) =>
        if eq (trm11, trm21) then eq (trm12, trm22) else false
    | (TRMany stp1, TRMany stp2) => (stp1 = stp2)
    | (_, _) => false
}

(* ****** ****** *)

(* end of [syntax.dats] *)
