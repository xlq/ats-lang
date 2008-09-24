(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS/Geizella - Unleashing the Power of Types!
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

// Time: October 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload Loc = "ats_location.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_posmark.sats"
staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

typedef loc_t = $Loc.location_t

(* ****** ****** *)

fn staexp_posmark (loc: loc_t):<fun> void =
  let
    val loc_begoff = $Loc.location_begpos_toff loc
    val loc_endoff = $Loc.location_endpos_toff loc
  in
    posmark_insert (loc_begoff, PMstaexp 0);
    posmark_insert (loc_endoff, PMstaexp 1);
  end

(* ****** ****** *)

fn s1exparg_posmark (s1a: s1exparg):<fun> void =
  staexp_posmark (s1a.s1exparg_loc)

fun s1exparglst_posmark (s1as: s1exparglst):<fun> void =
  case+ s1as of
  | cons (s1a, s1as) => begin
      s1exparg_posmark s1a; s1exparglst_posmark s1as
    end
  | nil () => ()

(* ****** ****** *)

implement p1at_posmark (p1t) = case+ p1t.p1at_node of
  | P1Tann (p1t, s1e) => staexp_posmark (s1e.s1exp_loc)
  | P1Tlist (npf, p1ts) => p1atlst_posmark p1ts
  | _ => ()

implement p1atlst_posmark (p1ts) = case+ p1ts of
  | cons (p1t, p1ts) => begin
      p1at_posmark p1t; p1atlst_posmark p1ts
    end
  | nil () => ()

(* ****** ****** *)

implement d1exp_posmark (d1e0) = case+ d1e0.d1exp_node of
  | D1Eann_effc (d1e, efc) => begin
      d1exp_posmark d1e
    end
  | D1Eann_fntp (d1e, ftp) => begin
      d1exp_posmark d1e
    end
  | D1Eann_type (d1e, s1e) => begin
      d1exp_posmark d1e; staexp_posmark (s1e.s1exp_loc)
    end
  | D1Eapp_dyn (d1e_fun, npf, d1es_arg) => begin
      d1exp_posmark d1e_fun; d1explst_posmark d1es_arg
    end
  | D1Eapp_sta (d1e_fun, s1as) => begin
      d1exp_posmark d1e_fun; s1exparglst_posmark s1as
    end
  | D1Elam_dyn (_, p1t, d1e) => begin
      p1at_posmark p1t; d1exp_posmark d1e
    end
  | D1Elam_met (loc_arg, s1es, d1e) => begin
      staexp_posmark loc_arg; d1exp_posmark d1e
    end
  | D1Elam_sta_ana (loc_arg, s1as, d1e) => begin
      staexp_posmark loc_arg; d1exp_posmark d1e
    end
  | D1Elam_sta_para (loc_arg, s1as, d1e) => begin
      staexp_posmark loc_arg; d1exp_posmark d1e
    end
  | D1Elam_sta_syn (loc_arg, s1as, d1e) => begin
      staexp_posmark loc_arg; d1exp_posmark d1e
    end
  | D1Elet (d1cs, d1e) => begin
      d1eclst_posmark d1cs; d1exp_posmark d1e
    end
  | D1Ewhere (d1e, d1cs) => begin
      d1eclst_posmark d1cs; d1exp_posmark d1e
    end
  | _ => ()

implement d1explst_posmark (d1es) = case+ d1es of
  | cons (d1e, d1es) => begin
      d1exp_posmark d1e; d1explst_posmark d1es
    end
  | nil () => ()

(* ****** ****** *)

fn d1cstdec_posmark (d1c: d1cstdec):<fun> void = begin
  staexp_posmark (d1c.d1cstdec_loc);
end

fun d1cstdeclst_posmark (d1cs: d1cstdeclst):<fun> void = case+ d1cs of
  | cons (d1c, d1cs) => begin
      d1cstdec_posmark d1c; d1cstdeclst_posmark d1cs
    end
  | nil () => ()

(* ****** ****** *)

fn f1undec_posmark (d1c: f1undec):<fun> void = begin
  d1exp_posmark d1c.f1undec_def;
end

fun f1undeclst_posmark (d1cs: f1undeclst):<fun> void = case+ d1cs of
  | cons (d1c, d1cs) => begin
      f1undec_posmark d1c; f1undeclst_posmark d1cs
    end
  | nil () => ()

(* ****** ****** *)

fn v1aldec_posmark (d1c: v1aldec):<fun> void = begin
  p1at_posmark d1c.v1aldec_pat;
  d1exp_posmark d1c.v1aldec_def;
end

fun v1aldeclst_posmark (d1cs: v1aldeclst):<fun> void = case+ d1cs of
  | cons (d1c, d1cs) => begin
      v1aldec_posmark d1c; v1aldeclst_posmark d1cs
    end
  | nil () => ()

(* ****** ****** *)

fn i1mpdec_posmark (d1c: i1mpdec):<fun> void = begin
  d1exp_posmark d1c.i1mpdec_def;
end

(* ****** ****** *)

implement d1ec_posmark (d1c0) =
  case+ d1c0.d1ec_node of
  | D1Cnone () => ()
  | D1Clist d1cs => d1eclst_posmark (d1cs)
  | D1Cdatsrts _ => staexp_posmark (d1c0.d1ec_loc)
  | D1Csrtdefs _ => staexp_posmark (d1c0.d1ec_loc)
  | D1Cstacons _ => staexp_posmark (d1c0.d1ec_loc)
  | D1Cstacsts _ => staexp_posmark (d1c0.d1ec_loc)
  | D1Csexpdefs _ => staexp_posmark (d1c0.d1ec_loc)
  | D1Csaspdec _ => staexp_posmark (d1c0.d1ec_loc)
  | D1Cdatdecs _ => staexp_posmark (d1c0.d1ec_loc)
  | D1Cexndecs _ => staexp_posmark (d1c0.d1ec_loc) 
  | D1Cdcstdecs (_, _, d1cs) => d1cstdeclst_posmark (d1cs)
  | D1Cextype _ => staexp_posmark (d1c0.d1ec_loc)
  | D1Cfundecs (_, _, d1cs) => f1undeclst_posmark d1cs
  | D1Cvaldecs (_, d1cs) => v1aldeclst_posmark d1cs
  | D1Cvaldecs_rec d1cs => v1aldeclst_posmark d1cs
  | D1Cimpdec d1c => i1mpdec_posmark d1c
  | _ => ()

implement d1eclst_posmark (d1cs0) =
  case+ d1cs0 of
  | list_cons (d1c, d1cs) => begin
      d1ec_posmark d1c; d1eclst_posmark d1cs
    end
  | list_nil () => ()

(* ****** ****** *)

(* end of [ats_dynexp1_posmark.dats] *)
