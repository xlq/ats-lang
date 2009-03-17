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

// Time: November 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

%{^

#include "ats_counter.cats" /* only needed for [ATS/Geizella] */

%}

(* ****** ****** *)

staload Lst = "ats_list.sats"
staload Stamp = "ats_stamp.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

typedef d2cst_struct = struct {
  d2cst_loc= loc_t
, d2cst_fil= fil_t
, d2cst_sym= sym_t
, d2cst_kind= $Syn.dcstkind
, d2cst_decarg= s2qualst // template arg
, d2cst_arilst= List int // arity
, d2cst_typ= s2exp // assigned type
, d2cst_ext= Stropt // external name
, d2cst_def= d2expopt // definition
, d2cst_stamp= stamp_t // unique stamp
, d2cst_hityp= Option (hityp_t) // type erasure
} // end of [d2cst_struct]

local

assume d2cst_t = [l:addr] (vbox (d2cst_struct @ l) | ptr l)

in // in of [local]

implement d2cst_make
  (loc, fil, id, dck, decarg, arilst, typ, ext) = let

val stamp = $Stamp.d2cst_stamp_make ()
val (pf_gc, pf | p) = ptr_alloc_tsz {d2cst_struct} (sizeof<d2cst_struct>)
prval () = free_gc_elim {d2cst_struct} (pf_gc)

val () = begin
p->d2cst_loc := loc;
p->d2cst_fil := fil;
p->d2cst_sym := id;
p->d2cst_kind := dck;
p->d2cst_decarg := decarg;
p->d2cst_arilst := arilst;
p->d2cst_typ := typ;
p->d2cst_ext := ext;
p->d2cst_def := None ();
p->d2cst_stamp := stamp;
p->d2cst_hityp := None ();
end // end of [val]

val (pfbox | ()) = vbox_make_view_ptr (pf | p)

in

(pfbox | p)

end // end of [d2cst_make]

implement d2cst_loc_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_loc end

implement d2cst_fil_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_fil end

implement d2cst_sym_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_sym end

implement d2cst_kind_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_kind end

implement d2cst_arilst_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_arilst end

implement d2cst_decarg_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_decarg end

implement d2cst_decarg_set (d2c, decarg) =
  let val (vbox pf | p) = d2c in p->d2cst_decarg := decarg end

implement d2cst_typ_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_typ end

implement d2cst_ext_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_ext end

implement d2cst_def_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_def end

implement d2cst_def_set (d2c, def) =
  let val (vbox pf | p) = d2c in p->d2cst_def := def end

implement d2cst_stamp_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_stamp end

// [d2cst_hityp_get] is declared in [ats_hiexp.sats]
implement d2cst_hityp_get (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_hityp end

(* ****** ****** *)

fn _lt_d2cst_d2cst
  (d2c1: d2cst_t, d2c2: d2cst_t): bool = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2c1 in p1->d2cst_stamp end
  val stamp2 =
    let val (vbox pf2 | p2) = d2c2 in p2->d2cst_stamp end
in
  $Stamp.lt_stamp_stamp (stamp1, stamp2)
end

implement lt_d2cst_d2cst (d2c1, d2c2) =
  $effmask_all ( _lt_d2cst_d2cst (d2c1, d2c2) )

//

fn _lte_d2cst_d2cst
  (d2c1: d2cst_t, d2c2: d2cst_t): bool = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2c1 in p1->d2cst_stamp end
  val stamp2 =
    let val (vbox pf2 | p2) = d2c2 in p2->d2cst_stamp end
in
  $Stamp.lte_stamp_stamp (stamp1, stamp2)
end

implement lte_d2cst_d2cst (d2c1, d2c2) =
  $effmask_all ( _lte_d2cst_d2cst (d2c1, d2c2) )

//

fn _eq_d2cst_d2cst
  (d2c1: d2cst_t, d2c2: d2cst_t): bool = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2c1 in p1->d2cst_stamp end
  val stamp2 =
    let val (vbox pf2 | p2) = d2c2 in p2->d2cst_stamp end
in
  $Stamp.eq_stamp_stamp (stamp1, stamp2)
end

implement eq_d2cst_d2cst (d2c1, d2c2) =
  $effmask_all ( _eq_d2cst_d2cst (d2c1, d2c2) )

//

fn _neq_d2cst_d2cst
  (d2c1: d2cst_t, d2c2: d2cst_t): bool = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2c1 in p1->d2cst_stamp end
  val stamp2 =
    let val (vbox pf2 | p2) = d2c2 in p2->d2cst_stamp end
in
  $Stamp.neq_stamp_stamp (stamp1, stamp2)
end

implement neq_d2cst_d2cst (d2c1, d2c2) =
  $effmask_all ( _neq_d2cst_d2cst (d2c1, d2c2) )

//

fn _compare_d2cst_d2cst
  (d2c1: d2cst_t, d2c2: d2cst_t): Sgn = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2c1 in p1->d2cst_stamp end
  val stamp2 =
    let val (vbox pf2 | p2) = d2c2 in p2->d2cst_stamp end
in
  $Stamp.compare_stamp_stamp (stamp1, stamp2)
end

implement compare_d2cst_d2cst (d2c1, d2c2) =
  $effmask_all ( _compare_d2cst_d2cst (d2c1, d2c2) )

(* ****** ****** *)

implement d2cst_is_fun (d2c) = let
  val knd = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_kind end
  ) // end of [val]
in
  $Syn.dcstkind_is_fun (knd)
end // end of [d2cst_is_fun]

implement d2cst_is_castfn (d2c) = let
  val knd = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_kind end
  ) // end of [val]
in
  $Syn.dcstkind_is_castfn (knd)
end // end of [d2cst_is_castfn]

//

implement d2cst_is_praxi (d2c) = let
  val knd = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_kind end
  ) // end of [val]
in
  $Syn.dcstkind_is_praxi (knd)
end // end of [d2cst_is_praxi]

implement d2cst_is_prfun (d2c) = let
  val knd = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_kind end
  ) // end of [val]
in
  $Syn.dcstkind_is_prfun (knd)
end // end of [d2cst_is_prfun]

implement d2cst_is_prval (d2c) = let
  val knd = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_kind end
  ) // end of [val]
in
  $Syn.dcstkind_is_prval (knd)
end // end of [d2cst_is_prval]

implement d2cst_is_proof (d2c) = let
  val knd = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_kind end
  ) // end of [val]
in
  $Syn.dcstkind_is_proof (knd)
end // end of [d2cst_is_proof]

//

implement d2cst_is_temp (d2c) = let
  val decarg = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_decarg end
  ) // end of [val]
in
  case+ decarg of list_cons _ => true | list_nil _ => false
end // end of [d2cst_is_temp]

end // end of [local] (for assuming d2cst_t)

(* ****** ****** *)

implement fprint_d2cst (pf_out | out, d2c) = begin
  $Sym.fprint_symbol (pf_out | out, d2cst_sym_get d2c)
end // end of [fprint_d2cst]

implement fprint_d2cstlst {m} (pf | out, d2cs) = let
  fun aux (out: &FILE m, i: int, d2cs: d2cstlst): void =
    case+ d2cs of
    | cons (d2c, d2cs) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_d2cst (pf | out, d2c); aux (out, i+1, d2cs)
    end
  | nil () => ()
in
  aux (out, 0, d2cs)
end // end of [fprint_d2cstlst]

(* ****** ****** *)

implement print_d2cst (d2c) = print_mac (fprint_d2cst, d2c)
implement prerr_d2cst (d2c) = prerr_mac (fprint_d2cst, d2c)

implement print_d2cstlst (d2cs) = print_mac (fprint_d2cstlst, d2cs)
implement prerr_d2cstlst (d2cs) = prerr_mac (fprint_d2cstlst, d2cs)

(* ****** ****** *)

// [d2cst_hityp_set] is declared in [ats_hiexp.sats]

extern typedef "d2cst_struct" = d2cst_struct

%{$

ats_void_type
ats_dynexp2_d2cst_hityp_set (ats_ptr_type d2c, ats_ptr_type ohit)
{
  ((d2cst_struct*)d2c)->atslab_d2cst_hityp = ohit ; return ;
}

%}

(* ****** ****** *)

(* end of [ats_dynexp2_dcst.dats] *)
