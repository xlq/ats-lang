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

// Time: January 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

implement fprint_s3item (pf | out, s3i) = begin
  case+ s3i of
  | S3ITEMcstr c3t => begin
      fprint (pf | out, "S3ITEMcstr(");
      fprint_c3str (pf | out, c3t);
      fprint (pf | out, ")")
    end
  | S3ITEMcstr_ref _ => begin
      fprint (pf | out, "S3ITEMcstr_ref(...)")
    end
  | S3ITEMdisj s3iss => begin
      fprint (pf | out, "S3ITEMdisj(...)")
    end
  | S3ITEMhypo h3p => begin
      fprint (pf | out, "S3ITEMhypo(");
      fprint_h3ypo (pf | out, h3p);
      fprint (pf | out, ")")
    end
  | S3ITEMsvar s2v => begin
      fprint (pf | out, "S3ITEMsvar(");
      fprint_s2var (pf | out, s2v);
      fprint (pf | out, ")")
    end
  | S3ITEMsVar s2V => let
      val () = fprint (pf | out, "S3ITEMsVar(")
      val () = fprint_s2Var (pf | out, s2V)
      val () = case+ s2Var_link_get (s2V) of
        | Some s2e => begin
            fprint (pf | out, "= "); fprint_s2exp (pf | out, s2e)
          end
        | None () => ()
      val () = fprint (pf | out, ")")
    in
      // empty
    end
end // end of [fprint_s3item]

implement fprint_s3itemlst {m} (pf | out, s3is) = let
  fun aux (out: &FILE m, i: int, s3is: s3itemlst): void =
    case+ s3is of
    | list_cons (s3i, s3is) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_s3item (pf | out, s3i); aux (out, i + 1, s3is)
      end
    | list_nil () => ()
in
  aux (out, 0, s3is)
end // end of [fprint_s3itemlst]

implement fprint_s3itemlstlst {m} (pf | out, s3iss) = let
  fun aux (out: &FILE m, i: int, s3iss: s3itemlstlst): void =
    case+ s3iss of
    | list_cons (s3is, s3iss) => begin
        if i > 0 then fprint (pf | out, "; ");
        fprint_s3itemlst (pf | out, s3is); aux (out, i + 1, s3iss)
      end
    | list_nil () => ()
in
  aux (out, 0, s3iss)
end // end of [fprint_s3itemlstlst]

(* ****** ****** *)

implement print_s3itemlst (s3is) = print_mac (fprint_s3itemlst, s3is)
implement prerr_s3itemlst (s3is) = prerr_mac (fprint_s3itemlst, s3is)

(* ****** ****** *)

implement fprint_c3strkind (pf | out, knd) = begin case+ knd of
  | C3STRKINDnone () => fprint (pf | out, "none")
  | C3STRKINDmetric_nat () => fprint (pf | out, "metric_nat")
  | C3STRKINDmetric_dec () => fprint (pf | out, "metric_dec")
  | C3STRKINDpattern_match_exhaustiveness _ => fprint (pf | out, "pattern")
  | C3STRKINDvarfin _ => fprint (pf | out, "varfin")
  | C3STRKINDloop (knd) => begin
      fprint (pf | out, "loop("); fprint (pf | out, knd); fprint (pf | out, ")")
    end
end // end of [fprint_c3strkind]

implement fprint_c3str (pf | out, c3t) = begin
  case+ c3t.c3str_node of
  | C3STRprop s2p => begin
      fprint (pf | out, "C3STRprop(");
      fprint_c3strkind (pf | out, c3t.c3str_kind);
      fprint (pf | out, "; ");
      fprint_s2exp (pf | out, s2p);
      fprint (pf | out, ")")
    end
  | C3STRitmlst s3is => begin
      fprint (pf | out, "C3STRitmlst(");
      fprint_c3strkind (pf | out, c3t.c3str_kind);
      fprint (pf | out, "; ");
      fprint_s3itemlst (pf | out, s3is);
      fprint (pf | out, ")")
    end
end // end of [fprint_c3str]

implement fprint_h3ypo (pf | out, h3p) = begin
  case+ h3p.h3ypo_node of
  | H3YPOprop s2p => begin
      fprint (pf | out, "H2YPOprop(");
      fprint_s2exp (pf | out, s2p);
      fprint (pf | out, ")")
    end
  | H3YPObind (s2v, s2p) => begin
      fprint (pf | out, "H2YPObind(");
      fprint_s2var (pf | out, s2v);
      fprint (pf | out, ", ");
      fprint_s2exp (pf | out, s2p);
      fprint (pf | out, ")")
    end
  | H3YPOeqeq (s2e1, s2e2) => begin
      fprint (pf | out, "H2YPOeqeq(");
      fprint_s2exp (pf | out, s2e1);
      fprint (pf | out, ", ");
      fprint_s2exp (pf | out, s2e2);
      fprint (pf | out, ")")
    end
end // end of [fprint_h3ypo]

(* ****** ****** *)

implement print_c3str (c3t) = print_mac (fprint_c3str, c3t)
implement prerr_c3str (c3t) = prerr_mac (fprint_c3str, c3t)

implement print_h3ypo (h3p) = print_mac (fprint_h3ypo, h3p)
implement prerr_h3ypo (h3p) = prerr_mac (fprint_h3ypo, h3p)

(* ****** ****** *)

(* end of [ats_trans3_env_print.dats] *)
