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

staload "ats_constraint.sats"

(* ****** ****** *)

implement fprint_s3aexp (pf | out, s3ae0) = case+ s3ae0 of
  | S3AEcst s2c => begin
      fprint (pf | out, "S3AEcst(");
      fprint (pf | out, s2c);
      fprint (pf | out, ")")
    end
  | S3AEexp s2e => begin
      fprint (pf | out, "S3AEexp(");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | S3AEvar s2v => begin
      fprint (pf | out, "S3AEvar(");
      fprint (pf | out, s2v);
      fprint (pf | out, ")")
    end
  | S3AEpadd (s3ae, s3ie) => begin
      fprint (pf | out, "S3AEpadd(");
      fprint (pf | out, s3ae);
      fprint (pf | out, "; ");
      fprint (pf | out, s3ie);
      fprint (pf | out, ")")
    end
  | S3AEnull => begin
      fprint (pf | out, "S3AEnull()")
    end

(* ****** ****** *)

implement fprint_s3bexp (pf | out, s3be0) = begin
  case+ s3be0 of
  | S3BEcst s2c => begin
      fprint (pf | out, "S3BEcst(");
      fprint (pf | out, s2c);
      fprint (pf | out, ")")
    end
  | S3BEexp s2e => begin
      fprint (pf | out, "S3BEexp(");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | S3BEvar s2v => begin
      fprint (pf | out, "S3BEvar(");
      fprint (pf | out, s2v);
      fprint (pf | out, ")")
    end
  | S3BEbool b => begin
      fprint (pf | out, "S3BEbool(");
      fprint (pf | out, b);
      fprint (pf | out, ")")
    end
  | S3BEbneg s3be => begin
      fprint (pf | out, "S3BEbneg(");
      fprint (pf | out, s3be);
      fprint (pf | out, ")")
    end
  | S3BEbadd (s3be1, s3be2) => begin
      fprint (pf | out, "S3BEbadd(");
      fprint (pf | out, s3be1);
      fprint (pf | out, "; ");
      fprint (pf | out, s3be2);
      fprint (pf | out, ")")
    end
  | S3BEbmul (s3be1, s3be2) => begin
      fprint (pf | out, "S3BEbmul(");
      fprint (pf | out, s3be1);
      fprint (pf | out, "; ");
      fprint (pf | out, s3be2);
      fprint (pf | out, ")")
    end
  | S3BEiexp (knd, s3ie) => begin
      fprint (pf | out, "S3BEiexp(");
      fprint (pf | out, "knd=");
      fprint (pf | out, knd);
      fprint (pf | out, "; ");
      fprint (pf | out, s3ie);
      fprint (pf | out, ")")
    end
end // end of [fprint_s3bexp]

implement fprint_s3bexplst {m} (pf | out, s3bes) = let
  fun aux (out: &FILE m, i: int, s3bes: s3bexplst)
    : void = begin case+ s3bes of
    | list_cons (s3be, s3bes) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_s3bexp (pf | out, s3be); aux (out, i+1, s3bes)
      end
    | list_nil () => ()
  end // end [aux]
in
  aux (out, 0, s3bes)
end // end of [fprint_s3bexplst]

(* ****** ****** *)

implement fprint_s3iexp (pf | out, s3ie0) = begin
  case+ s3ie0 of
  | S3IEcst s2c => begin
      fprint (pf | out, "S3IEcst(");
      fprint (pf | out, s2c);
      fprint (pf | out, ")")
    end
  | S3IEexp s2e => begin
      fprint (pf | out, "S3IEexp(");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | S3IEvar s2v => begin
      fprint (pf | out, "S3IEvar(");
      fprint (pf | out, s2v);
      fprint (pf | out, ")")
    end
  | S3IEint i => begin
      fprint (pf | out, "S3IEint(");
      fprint (pf | out, i);
      fprint (pf | out, ")")
    end
  | S3IEintinf i => begin
      fprint (pf | out, "S3IEintinf(");
      $IntInf.fprint_intinf (pf | out, i);
      fprint (pf | out, ")")
    end
  | S3IEineg (s3ie) => begin
      fprint (pf | out, "S3IEineg(");
      fprint (pf | out, s3ie);
      fprint (pf | out, ")")
    end
  | S3IEiadd (s3ie1, s3ie2) => begin
      fprint (pf | out, "S3IEiadd(");
      fprint (pf | out, s3ie1);
      fprint (pf | out, "; ");
      fprint (pf | out, s3ie2);
      fprint (pf | out, ")")
    end
  | S3IEisub (s3ie1, s3ie2) => begin
      fprint (pf | out, "S3IEisub(");
      fprint (pf | out, s3ie1);
      fprint (pf | out, "; ");
      fprint (pf | out, s3ie2);
      fprint (pf | out, ")")
    end
  | S3IEimul (s3ie1, s3ie2) => begin
      fprint (pf | out, "S3IEimul(");
      fprint (pf | out, s3ie1);
      fprint (pf | out, "; ");
      fprint (pf | out, s3ie2);
      fprint (pf | out, ")")
    end
  | S3IEpdiff (s3ae1, s3ae2) => begin
      fprint (pf | out, "S3IEpdiff(");
      fprint (pf | out, s3ae1);
      fprint (pf | out, "; ");
      fprint (pf | out, s3ae2);
      fprint (pf | out, ")")
    end
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
