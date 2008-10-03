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

implement fprint_s3item (pf | out, s3i) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s3i of
  | S3ITEMcstr c3t => begin
      strpr "S3ITEMcstr("; fprint_c3str (pf | out, c3t); strpr ")"
    end
  | S3ITEMcstr_ref _ => begin
      fprint1_string (pf | out, "S3ITEMcstr_ref(...)")
    end
  | S3ITEMdisj s3iss => begin
      fprint1_string (pf | out, "S3ITEMdisj(...)")
    end
  | S3ITEMhypo h3p => begin
      strpr "S3ITEMhypo("; fprint_h3ypo (pf | out, h3p); strpr ")"
    end
  | S3ITEMsvar s2v => begin
      strpr "S3ITEMsvar("; fprint_s2var (pf | out, s2v); strpr ")"
    end
  | S3ITEMsVar s2V => let
      val () = strpr "S3ITEMsVar("
      val () = fprint_s2Var (pf | out, s2V)
      val () = case+ s2Var_link_get (s2V) of
        | Some s2e => begin
            strpr "= "; fprint_s2exp (pf | out, s2e)
          end
        | None () => ()
      val () = strpr ")"
    in
      // empty
    end
end // end of [fprint_s3item]

implement fprint_s3itemlst {m} (pf | out, s3is) = let
  fun aux (out: &FILE m, i: int, s3is: s3itemlst): void =
    case+ s3is of
    | list_cons (s3i, s3is) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
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
        if i > 0 then fprint1_string (pf | out, "; ");
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

implement fprint_c3strkind (pf | out, knd) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ knd of
  | C3STRKINDnone () => strpr "none"
  | C3STRKINDmetric_nat () => strpr "metric_nat"
  | C3STRKINDmetric_dec () => strpr "metric_dec"
  | C3STRKINDpattern_match_exhaustiveness _ => strpr "pattern"
  | C3STRKINDvarfin _ => strpr "varfin"
  | C3STRKINDloop (knd) => begin
      strpr "loop("; fprint1_int (pf | out, knd); strpr ")"
    end
end // end of [fprint_c3strkind]

implement fprint_c3str (pf | out, c3t) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ c3t.c3str_node of
  | C3STRprop s2p => begin
      strpr "C3STRprop(";
      fprint_c3strkind (pf | out, c3t.c3str_kind);
      strpr "; ";
      fprint_s2exp (pf | out, s2p);
      strpr ")"
    end // end of [C3STRprop]
  | C3STRitmlst s3is => begin
      strpr "C3STRitmlst(";
      fprint_c3strkind (pf | out, c3t.c3str_kind);
      strpr "; ";
      fprint_s3itemlst (pf | out, s3is);
      strpr ")"
    end // end of [C3STRitmlst]
end // end of [fprint_c3str]

implement fprint_h3ypo (pf | out, h3p) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ h3p.h3ypo_node of
  | H3YPOprop s2p => begin
      strpr "H2YPOprop("; fprint_s2exp (pf | out, s2p); strpr ")"
    end // end of [H3YPOprop]
  | H3YPObind (s2v, s2p) => begin
      strpr "H2YPObind(";
      fprint_s2var (pf | out, s2v);
      strpr ", ";
      fprint_s2exp (pf | out, s2p);
      strpr ")"
    end // end of [H3YPObind]
  | H3YPOeqeq (s2e1, s2e2) => begin
      strpr "H2YPOeqeq(";
      fprint_s2exp (pf | out, s2e1);
      strpr ", ";
      fprint_s2exp (pf | out, s2e2);
      strpr ")"
    end // end of [H3YPOeqeq]
end // end of [fprint_h3ypo]

(* ****** ****** *)

implement print_c3str (c3t) = print_mac (fprint_c3str, c3t)
implement prerr_c3str (c3t) = prerr_mac (fprint_c3str, c3t)

implement print_h3ypo (h3p) = print_mac (fprint_h3ypo, h3p)
implement prerr_h3ypo (h3p) = prerr_mac (fprint_h3ypo, h3p)

(* ****** ****** *)

(* end of [ats_trans3_env_print.dats] *)
