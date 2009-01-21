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

staload Err = "ats_error.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_stadyncst2.sats"

(* ****** ****** *)

overload prerr with $Loc.prerr_location

(* ****** ****** *)

implement atlin_is_at (atlin: uint): bool =
  if (atlin land 0x2U) > 0U then true else false

implement atlin_is_lin (atlin: uint): bool =
  if (atlin land 0x1U) > 0U then true else false

(* ****** ****** *)

implement d2var_readize (s2e_v, d2v) = let
  val () = d2var_lin_set (d2v, ~1) // nonlinear
  val () = d2var_mastyp_set (
    d2v, s2expopt_readize (s2e_v, d2var_mastyp_get (d2v))
  )
  val () = d2var_typ_set (
    d2v, s2expopt_readize (s2e_v, d2var_typ_get (d2v))
  )
in
  // empty
end // end of [d2var_readize]

implement d2varlst_readize (s2e_v, d2vs) = begin case+ d2vs of
  | list_cons (d2v, d2vs) => begin
      d2var_readize (s2e_v, d2v); d2varlst_readize (s2e_v, d2vs)
    end
  | list_nil () => ()
end // end of [d2varlst_readize]

(* ****** ****** *)

implement d2exp_is_varlamcst (d2e0) = begin
  case+ d2e0.d2exp_node of
  | D2Evar _ => true
  | D2Elam_dyn _ => true
  | D2Echar _ => true
  | D2Eint _ => true
  | D2Estring _ => true
  | D2Etop _ => true
  | _ => false
end // end of [d2exp_is_varlamcst]

(* ****** ****** *)

implement d2exp_var_is_ptr (d2e0) = begin
  case+ d2e0.d2exp_node of
  | D2Evar d2v => begin case+ d2var_typ_get d2v of
    | Some s2e => s2cstref_exp_equ (Ptr_addr_type, s2e)
    | None () => false
    end
  | _ => begin
      prerr d2e0.d2exp_loc;
      prerr ": Internal Error: d2exp_var_is_ptr: d2e0 = ";
      prerr d2e0; prerr_newline ();
      $Err.abort {bool} ()
    end
end // end of [d2exp_var_is_ptr]

(* ****** ****** *)

fn d2exp_seq_is_raised (d2es: d2explst): bool = let
  fun aux (d2e: d2exp, d2es: d2explst): bool = case+ d2es of
    | list_cons (d2e, d2es) => aux (d2e, d2es)
    | list_nil () => d2exp_is_raised d2e
in
  case+ d2es of
  | list_cons (d2e, d2es) => aux (d2e, d2es)
  | list_nil () => false
end // end of [d2exp_seq_is_raised]

fun c2laulst_is_raised (c2ls: c2laulst): bool = begin
  case+ c2ls of
  | list_cons (c2l, c2ls) => begin
      if c2lau_is_raised c2l then c2laulst_is_raised c2ls else false
    end
  | list_nil () => true
end // end of [c2laulst_is_raised]

implement d2exp_is_raised (d2e0) = begin
  case+ d2e0.d2exp_node of
  | D2Eann_type (d2e, _) => d2exp_is_raised d2e
  | D2Eann_seff (d2e, _) => d2exp_is_raised d2e
  | D2Ecaseof (_, _, _, _, c2ls) => c2laulst_is_raised c2ls
  | D2Eif (_(*inv*), _(*cond*), d2e1, od2e2) => begin case+ od2e2 of
    | Some d2e2 => begin
        if d2exp_is_raised d2e1 then d2exp_is_raised d2e2 else false
      end
    | None () => false
    end
  | D2Elet (d2cs, d2e) => d2exp_is_raised d2e
  | D2Eloopexn i => true
  | D2Eraise _ => true
  | D2Eseq d2es => d2exp_seq_is_raised d2es
  | D2Ewhere (d2e, _) => d2exp_is_raised d2e
  | _ => false
end // end of [d2exp_is_raise]

implement c2lau_is_raised (c2l) = begin
  if c2l.c2lau_neg > 0 then true else d2exp_is_raised c2l.c2lau_exp
end // end of [c2lau_is_raised]

(* ****** ****** *)

(* end of [ats_dynexp2_util.dats] *)
