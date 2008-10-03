(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS/Anairiats - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
 * Free Software Foundation; either version 3, or (at  your  option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

// Time: February 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

(* for representing and handling constraints *)

(* ****** ****** *)

staload IntInf = "ats_intinf.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_constraint.sats"

(* ****** ****** *)

implement fprint_s3aexp (pf | out, s3ae0) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s3ae0 of
  | S3AEcst s2c => begin
      strpr "S3AEcst("; fprint_s2cst (pf | out, s2c); strpr ")"
    end
  | S3AEexp s2e => begin
      strpr "S3AEexp("; fprint_s2exp (pf | out, s2e); strpr ")"
    end
  | S3AEvar s2v => begin
      strpr "S3AEvar("; fprint_s2var (pf | out, s2v); strpr ")"
    end
  | S3AEpadd (s3ae, s3ie) => begin
      strpr "S3AEpadd(";
      fprint_s3aexp (pf | out, s3ae);
      strpr "; ";
      fprint_s3iexp (pf | out, s3ie);
      strpr ")"
    end // end of [S3AEpadd]
  | S3AEnull => begin
      fprint1_string (pf | out, "S3AEnull()")
    end
end // end of [fprint_s3aexp]

(* ****** ****** *)

implement fprint_s3bexp (pf | out, s3be0) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s3be0 of
  | S3BEcst s2c => begin
      strpr "S3BEcst("; fprint_s2cst (pf | out, s2c); strpr ")"
    end
  | S3BEexp s2e => begin
      strpr "S3BEexp("; fprint_s2exp (pf | out, s2e); strpr ")"
    end
  | S3BEvar s2v => begin
      strpr "S3BEvar("; fprint_s2var (pf | out, s2v); strpr ")"
    end
  | S3BEbool b => begin
      strpr "S3BEbool("; fprint1_bool (pf | out, b); strpr ")"
    end
  | S3BEbneg s3be => begin
      strpr "S3BEbneg("; fprint_s3bexp (pf | out, s3be); strpr ")"
    end
  | S3BEbadd (s3be1, s3be2) => begin
      strpr "S3BEbadd(";
      fprint_s3bexp (pf | out, s3be1);
      strpr "; ";
      fprint_s3bexp (pf | out, s3be2);
      strpr ")"
    end // end of [S3BEbadd]
  | S3BEbmul (s3be1, s3be2) => begin
      strpr "S3BEbmul(";
      fprint_s3bexp (pf | out, s3be1);
      strpr "; ";
      fprint_s3bexp (pf | out, s3be2);
      strpr ")"
    end // end of [S3BEbmul]
  | S3BEiexp (knd, s3ie) => begin
      strpr "S3BEiexp(";
      strpr "knd=";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_s3iexp (pf | out, s3ie);
      strpr ")"
    end // end of [S3BEiexp]
end // end of [fprint_s3bexp]

implement fprint_s3bexplst {m} (pf | out, s3bes) = let
  fun aux (out: &FILE m, i: int, s3bes: s3bexplst)
    : void = begin case+ s3bes of
    | list_cons (s3be, s3bes) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_s3bexp (pf | out, s3be); aux (out, i+1, s3bes)
      end
    | list_nil () => ()
  end // end [aux]
in
  aux (out, 0, s3bes)
end // end of [fprint_s3bexplst]

(* ****** ****** *)

implement fprint_s3iexp (pf | out, s3ie0) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s3ie0 of
  | S3IEcst s2c => begin
      strpr "S3IEcst("; fprint_s2cst (pf | out, s2c); strpr ")"
    end
  | S3IEexp s2e => begin
      strpr "S3IEexp("; fprint_s2exp (pf | out, s2e); strpr ")"
    end
  | S3IEvar s2v => begin
      strpr "S3IEvar("; fprint_s2var (pf | out, s2v); strpr ")"
    end
  | S3IEint i => begin
      strpr "S3IEint("; fprint1_int (pf | out, i); strpr ")"
    end
  | S3IEintinf i => begin
      strpr "S3IEintinf(";
      $IntInf.fprint_intinf (pf | out, i);
      strpr ")"
    end // end of [S2IEintinf]
  | S3IEineg (s3ie) => begin
      strpr "S3IEineg("; fprint_s3iexp (pf | out, s3ie); strpr ")"
    end
  | S3IEiadd (s3ie1, s3ie2) => begin
      strpr "S3IEiadd(";
      fprint_s3iexp (pf | out, s3ie1);
      strpr "; ";
      fprint_s3iexp (pf | out, s3ie2);
      strpr ")"
    end // end of [S3IEiadd]
  | S3IEisub (s3ie1, s3ie2) => begin
      strpr "S3IEisub(";
      fprint_s3iexp (pf | out, s3ie1);
      strpr "; ";
      fprint_s3iexp (pf | out, s3ie2);
      strpr ")"
    end // end of [S3IEisub]
  | S3IEimul (s3ie1, s3ie2) => begin
      strpr "S3IEimul(";
      fprint_s3iexp (pf | out, s3ie1);
      strpr "; ";
      fprint_s3iexp (pf | out, s3ie2);
      strpr ")"
    end // end of [S3IEimul]
  | S3IEpdiff (s3ae1, s3ae2) => begin
      strpr "S3IEpdiff(";
      fprint_s3aexp (pf | out, s3ae1);
      strpr "; ";
      fprint_s3aexp (pf | out, s3ae2);
      strpr ")"
    end // end of [S3IEdiff]
end // end of [fprint_s3iexp]

(* ****** ****** *)

implement print_s3aexp (s3ae) = print_mac (fprint_s3aexp, s3ae)
implement prerr_s3aexp (s3ae) = prerr_mac (fprint_s3aexp, s3ae)

implement print_s3bexp (s3be) = print_mac (fprint_s3bexp, s3be)
implement prerr_s3bexp (s3be) = prerr_mac (fprint_s3bexp, s3be)

implement print_s3bexplst (s3bes) = print_mac (fprint_s3bexplst, s3bes)
implement prerr_s3bexplst (s3bes) = prerr_mac (fprint_s3bexplst, s3bes)

implement print_s3iexp (s3ie) = print_mac (fprint_s3iexp, s3ie)
implement prerr_s3iexp (s3ie) = prerr_mac (fprint_s3iexp, s3ie)

(* ****** ****** *)

(* end of [ats_constraint_print.dats] *)
