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

// Time: October 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"

(* ****** ****** *)

typedef d2con_struct = struct { (* builtin or abstract *)
  d2con_loc= loc_t // location
, d2con_fil= fil_t // filename
, d2con_sym= sym_t // the name
, d2con_scst= s2cst_t // datatype
, d2con_vwtp= int //
, d2con_qua= List @(s2varlst, s2explst) // quantifiers
, d2con_npf= int // pfarity
, d2con_arg= s2explst // views or viewtypes
, d2con_arity_full= int // full arity
, d2con_arity_real= int // real arity after erasure
, d2con_ind= Option s2explst // indexes
, d2con_typ= s2exp // type for dynamic constructor
, d2con_tag= int // tag for dynamic constructor
, d2con_stamp= stamp_t // uniqueness
}

(* ****** ****** *)

local

assume d2con_t = [l:addr] (vbox (d2con_struct @ l) | ptr l)

in // in of [local]

implement d2con_make
  (loc, fil, id, s2c, vwtp, qua, npf, arg, ind) = let

val stamp = $Stamp.d2con_stamp_make ()
val arity_full = $Lst.list_length (arg)
val arity_real = let
  fun aux1 (i: int, s2es: s2explst): s2explst = case+ s2es of
    | list_cons (_, s2es1) => if i > 0 then aux1 (i-1, s2es1) else s2es
    | list_nil () => list_nil ()
  fun aux2 (i: int, s2es: s2explst): int = case+ s2es of
    | list_cons (s2e, s2es1) => begin
        if s2exp_is_proof s2e then aux2 (i, s2es1) else aux2 (i+1, s2es1)
      end
    | list_nil () => i
in
  aux2 (0, aux1 (npf, arg))
end

val s2e_d2c = let
  fun aux (s2e: s2exp, s2vpss: List @(s2varlst, s2explst)): s2exp =
    case+ s2vpss of
    | list_cons (s2vps, s2vpss) => begin
        s2exp_uni (s2vps.0, s2vps.1, aux (s2e, s2vpss))
      end
    | list_nil () => s2e
  val s2e_res = case+ ind of
    | Some s2es => s2exp_cstapp (s2c, s2es) | None () => s2exp_cst (s2c)
in
  aux (s2exp_confun (npf, arg, s2e_res), qua)
end

val (pf_gc, pf | p) = ptr_alloc_tsz {d2con_struct} (sizeof<d2con_struct>)

val () = begin
p->d2con_loc := loc;
p->d2con_fil := fil;
p->d2con_sym := id;
p->d2con_scst := s2c;
p->d2con_vwtp := vwtp;
p->d2con_qua := qua;
p->d2con_npf := npf;
p->d2con_arg := arg;
p->d2con_arity_full := arity_full;
p->d2con_arity_real := arity_real;
p->d2con_ind := ind;
p->d2con_typ := s2e_d2c;
p->d2con_tag := ~1;
p->d2con_stamp := stamp
end

val (pfbox | ()) = vbox_make_view_ptr_gc (pf_gc, pf | p)

in

(pfbox | p)

end // end of [d2con_make]

(* ****** ****** *)

implement d2con_fil_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_fil end

implement d2con_sym_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_sym end

implement d2con_scst_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_scst end

implement d2con_vwtp_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_vwtp end

implement d2con_qua_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_qua end

implement d2con_npf_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_npf end

implement d2con_arg_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_arg end

implement d2con_arity_full_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_arity_full end

implement d2con_arity_real_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_arity_real end

implement d2con_typ_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_typ end

implement d2con_ind_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_ind end

implement d2con_tag_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_tag end

implement d2con_tag_set (d2c, tag) =
  let val (vbox pf | p) = d2c in p->d2con_tag := tag end

implement d2con_stamp_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_stamp end

(* ****** ****** *)

implement lt_d2con_d2con (d2c1, d2c2) = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2c1 in p1->d2con_stamp end
  val stamp2 =
    let val (vbox pf2 | p2) = d2c2 in p2->d2con_stamp end
in
  $Stamp.lt_stamp_stamp (stamp1, stamp2)
end

implement lte_d2con_d2con (d2c1, d2c2) = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2c1 in p1->d2con_stamp end
  val stamp2 =
    let val (vbox pf2 | p2) = d2c2 in p2->d2con_stamp end
in
  $Stamp.lte_stamp_stamp (stamp1, stamp2)
end

implement eq_d2con_d2con (d2c1, d2c2) = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2c1 in p1->d2con_stamp end
  val stamp2 =
    let val (vbox pf2 | p2) = d2c2 in p2->d2con_stamp end
in
  $Stamp.eq_stamp_stamp (stamp1, stamp2)
end

implement neq_d2con_d2con (d2c1, d2c2) = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2c1 in p1->d2con_stamp end
  val stamp2 =
    let val (vbox pf2 | p2) = d2c2 in p2->d2con_stamp end
in
  $Stamp.neq_stamp_stamp (stamp1, stamp2)
end

//

fn _compare_d2con_d2con
  (d2c1: d2con_t, d2c2: d2con_t) = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2c1 in p1->d2con_stamp end
  val stamp2 =
    let val (vbox pf2 | p2) = d2c2 in p2->d2con_stamp end
in
  $Stamp.compare_stamp_stamp (stamp1, stamp2)
end

implement compare_d2con_d2con (d2c1, d2c2) =
  $effmask_all ( _compare_d2con_d2con (d2c1, d2c2) )

//

#define D2CON_TAG_EXN ~1
implement d2con_is_exn (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_tag = D2CON_TAG_EXN end

#define D2CON_TAG_MSG ~2
implement d2con_is_msg (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_tag = D2CON_TAG_MSG end

end // end of [local] (for assuming d2con_t)

(* ****** ****** *)

implement fprint_d2con (pf_out | out, d2c) = begin
  $Sym.fprint_symbol (pf_out | out, d2con_sym_get d2c)
end

implement fprint_d2conlst {m} (pf | out, d2cs) = let
  fun aux (out: &FILE m, i:int, d2cs: d2conlst)
    : void = begin case+ d2cs of
    | D2CONLSTcons (d2c, d2cs) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_d2con (pf | out, d2c); aux (out, i+1, d2cs)
      end
    | D2CONLSTnil () => ()
  end // end of [aux]
in
  aux (out, 0, d2cs)
end // end of [fprint_d2conlst]

(* ****** ****** *)

implement print_d2con (d2c) = print_mac (fprint_d2con, d2c)
implement prerr_d2con (d2c) = prerr_mac (fprint_d2con, d2c)

implement print_d2conlst (d2cs) = print_mac (fprint_d2conlst, d2cs)
implement prerr_d2conlst (d2cs) = prerr_mac (fprint_d2conlst, d2cs)

(* ****** ****** *)

(* end of [ats_staexp2_dcon.dats] *)
