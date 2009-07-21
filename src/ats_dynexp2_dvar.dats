(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

// Time: November 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

%{^

#include "ats_counter.cats" /* only needed for [ATS/Geizella] */

%}

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Lst = "ats_list.sats"
staload Stamp = "ats_stamp.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_stadyncst2.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

typedef d2var_struct = struct {
  d2var_loc= loc_t // first location
, d2var_sym= sym_t // name
, d2var_lev= int // toplevel: 0
, d2var_lin= int // nonlinear (-1) and linear (>=0)
, d2var_isfix= bool // is fix-variable?
, d2var_isprf= bool // is proof?
, d2var_decarg= s2qualst // template arg
, d2var_addr= s2expopt //
, d2var_view= d2varopt // 
, d2var_fin= d2var_fin //
, d2var_typ= s2expopt //
, d2var_mastyp= s2expopt //
, d2var_count= int //
, d2var_stamp= stamp_t // uniqueness stamp
}

local

assume d2var_t = [l:addr] (vbox (d2var_struct @ l) | ptr l)

in // in of [local]

implement d2var_make (loc, id) = let

val stamp = $Stamp.d2var_stamp_make ()
val (pf_gc, pf | p) = ptr_alloc_tsz {d2var_struct} (sizeof<d2var_struct>)
prval () = free_gc_elim {d2var_struct} (pf_gc)

val () = begin
p->d2var_loc := loc;
p->d2var_sym := id;
p->d2var_lev := ~1;
p->d2var_lin := ~1;
p->d2var_isfix := false;
p->d2var_isprf := false;
p->d2var_decarg := list_nil ();
p->d2var_addr := None ();
p->d2var_view := D2VAROPTnone ();
p->d2var_fin := D2VARFINnone ();
p->d2var_typ := None ();
p->d2var_mastyp := None ();
p->d2var_count := 0;
p->d2var_stamp := stamp
end // end of [val]

val (pfbox | ()) = vbox_make_view_ptr (pf | p)

in

(pfbox | p)

end // end of [d2var_make]

implement d2var_make_any (loc) = begin
  d2var_make (loc, $Sym.symbol_UNDERSCORE)
end // end of [d2var_make_any]

(* ****** ****** *)

implement d2var_loc_get (d2v) =
  let val (vbox pf | p) = d2v in p->d2var_loc end

implement d2var_sym_get (d2v) =
  let val (vbox pf | p) = d2v in p->d2var_sym end

implement d2var_isfix_get (d2v) =
  let val (vbox pf | p) = d2v in p->d2var_isfix end

implement d2var_isfix_set (d2v, isfix) =
  let val (vbox pf | p) = d2v in p->d2var_isfix := isfix end

implement d2var_isprf_get (d2v) =
  let val (vbox pf | p) = d2v in p->d2var_isprf end

implement d2var_isprf_set (d2v, isprf) =
  let val (vbox pf | p) = d2v in p->d2var_isprf := isprf end

implement d2var_lev_get (d2v) =
  let val (vbox pf | p) = d2v in p->d2var_lev end

implement d2var_lev_set (d2v, lev) =
  let val (vbox pf | p) = d2v in p->d2var_lev := lev end

implement d2var_lin_get (d2v) =
  let val (vbox pf | p) = d2v in p->d2var_lin end

implement d2var_lin_set (d2v, lin) =
  let val (vbox pf | p) = d2v in p->d2var_lin := lin end

implement d2var_lin_inc (d2v) =
  let val (vbox pf | p) = d2v in p->d2var_lin := 1 + p->d2var_lin end

implement d2var_decarg_get (d2v) =
  let val (vbox pf | p) = d2v in p->d2var_decarg end

implement d2var_decarg_set (d2v, decarg) =
  let val (vbox pf | p) = d2v in p->d2var_decarg := decarg end

implement d2var_addr_get (d2v) =
  let val (vbox pf | p) = d2v in p->d2var_addr end

implement d2var_addr_set (d2v, os2e_addr) =
  let val (vbox pf | p) = d2v in p->d2var_addr := os2e_addr end

implement d2var_view_get (d2v) =
  let val (vbox pf | p) = d2v in p->d2var_view end

implement d2var_view_set (d2v, od2v_view) =
  let val (vbox pf | p) = d2v in p->d2var_view := od2v_view end

implement d2var_fin_get (d2v) =
  let val (vbox pf | p) = d2v in p->d2var_fin end

implement d2var_fin_set (d2v, fin) =
  let val (vbox pf | p) = d2v in p->d2var_fin := fin end

implement d2var_typ_get (d2v) =
  let val (vbox pf | p) = d2v in p->d2var_typ end

implement d2var_typ_set (d2v, os2e) =
  let val (vbox pf | p) = d2v in p->d2var_typ := os2e end

implement d2var_mastyp_get (d2v) =
  let val (vbox pf | p) = d2v in p->d2var_mastyp end

implement d2var_mastyp_set (d2v, os2e) =
  let val (vbox pf | p) = d2v in p->d2var_mastyp := os2e end

implement d2var_count_get (d2v) =
  let val (vbox pf | p) = d2v in p->d2var_count end
// end of [d2var_count_get]

implement d2var_count_inc (d2v) = let
  val (vbox pf | p) = d2v; val n = p->d2var_count in
  p->d2var_count := n + 1
end (* end of [d2var_count_inc] *)

implement d2var_stamp_get (d2v) =
  let val (vbox pf | p) = d2v in p->d2var_stamp end
// end of [d2var_stamp_get]

(* ****** ****** *)

fn _lt_d2var_d2var
  (d2v1: d2var_t, d2v2: d2var_t): bool = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2v1 in p1->d2var_stamp end
  val stamp2 =
    let val (vbox pf2 | p2) = d2v2 in p2->d2var_stamp end
in
  $Stamp.lt_stamp_stamp (stamp1, stamp2)
end

implement lt_d2var_d2var (d2v1, d2v2) =
  $effmask_all ( _lt_d2var_d2var (d2v1, d2v2) )

fn _lte_d2var_d2var
  (d2v1: d2var_t, d2v2: d2var_t): bool = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2v1 in p1->d2var_stamp end
  val stamp2 =
    let val (vbox pf2 | p2) = d2v2 in p2->d2var_stamp end
in
  $Stamp.lte_stamp_stamp (stamp1, stamp2)
end

implement lte_d2var_d2var (d2v1, d2v2) =
  $effmask_all ( _lte_d2var_d2var (d2v1, d2v2) )

fn _eq_d2var_d2var
  (d2v1: d2var_t, d2v2: d2var_t): bool = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2v1 in p1->d2var_stamp end
  val stamp2 =
    let val (vbox pf2 | p2) = d2v2 in p2->d2var_stamp end
in
  $Stamp.eq_stamp_stamp (stamp1, stamp2)
end

implement eq_d2var_d2var (d2v1, d2v2) =
  $effmask_all ( _eq_d2var_d2var (d2v1, d2v2) )

fn _neq_d2var_d2var
  (d2v1: d2var_t, d2v2: d2var_t): bool = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2v1 in p1->d2var_stamp end
  val stamp2 =
    let val (vbox pf2 | p2) = d2v2 in p2->d2var_stamp end
in
  $Stamp.neq_stamp_stamp (stamp1, stamp2)
end

implement neq_d2var_d2var (d2v1, d2v2) =
  $effmask_all ( _neq_d2var_d2var (d2v1, d2v2) )

fn _compare_d2var_d2var
  (d2v1: d2var_t, d2v2: d2var_t): Sgn = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2v1 in p1->d2var_stamp end
  val stamp2 =
    let val (vbox pf2 | p2) = d2v2 in p2->d2var_stamp end
in
  $Stamp.compare_stamp_stamp (stamp1, stamp2)
end

implement compare_d2var_d2var (d2v1, d2v2) =
  $effmask_all ( _compare_d2var_d2var (d2v1, d2v2) )

(* ****** ****** *)

end // end of [local] (for assuming d2var_t)

(* ****** ****** *)

implement d2var_typ_get_some (loc0, d2v) = begin
  case+ d2var_typ_get d2v of
  | Some s2e => s2e
  | None () => begin
      $Loc.prerr_location loc0;
      prerr ": error(3)";
      prerr ": there is no type for the dynamic variable [";
      prerr d2v;
      prerr "].";
      prerr_newline ();
      $Err.abort {s2exp} ()
    end
end // end of [d2var_typ_get_some]

implement d2var_mastyp_get_some (loc0, d2v) = begin
  case+ d2var_mastyp_get d2v of
  | Some s2e => s2e
  | None () => begin
      $Loc.prerr_location loc0;
      prerr ": error(3)";
      prerr ": there is no master type for the dynamic variable [";
      prerr d2v;
      prerr "].";
      prerr_newline ();
      $Err.abort {s2exp} ()
    end
end // end of [d2var_mastyp_get_some]

implement d2var_addr_get_some (loc0, d2v) = begin
  case+ d2var_addr_get d2v of
  | Some s2e => s2e
  | None () => begin
      $Loc.prerr_location loc0;
      prerr ": Internal Error: d2var_addr_get_some: ";
      prerr ": there is no address for the dynamic variable [";
      prerr d2v;
      prerr "].";
      prerr_newline ();
      $Err.abort {s2exp} ()
    end
end // end of [d2var_addr_get_some]

implement d2var_view_get_some (loc0, d2v) = begin
  case+ d2var_view_get d2v of
  | D2VAROPTsome d2v_view => d2v_view
  | D2VAROPTnone () => begin
      $Loc.prerr_location loc0;
      prerr ": Internal Error: d2var_view_get_some: ";
      prerr ": there is no view attached to the dynamic variable [";
      prerr d2v;
      prerr "].";
      prerr_newline ();
      $Err.abort {d2var_t} ()
    end
end // end of [d2var_addr_get_some]

(* ****** ****** *)

implement fprint_d2var (pf_out | out, d2v) = begin
  $Sym.fprint_symbol (pf_out | out, d2var_sym_get d2v)
end // end of [fprint_d2var]

implement fprint_d2varlst {m} (pf | out, d2vs) = let
  fun aux (out: &FILE m, i: int, d2vs: d2varlst): void =
    case+ d2vs of
    | cons (d2v, d2vs) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_d2var (pf | out, d2v); aux (out, i+1, d2vs)
      end
    | nil () => ()
in
  aux (out, 0, d2vs)
end // end of [fprint_d2varlst]

//

implement print_d2var (d2v) = print_mac (fprint_d2var, d2v)
implement prerr_d2var (d2v) = prerr_mac (fprint_d2var, d2v)

implement print_d2varlst (d2vs) = print_mac (fprint_d2varlst, d2vs)
implement prerr_d2varlst (d2vs) = prerr_mac (fprint_d2varlst, d2vs)

(* ****** ****** *)

implement d2var_is_linear (d2v) = (d2var_lin_get d2v >= 0)
implement d2var_is_mutable (d2v) =
  case+ d2var_view_get d2v of D2VAROPTsome _ => true | D2VAROPTnone () => false

(* ****** ****** *)

implement d2var_typ_reset (d2v, s2e) = begin
  d2var_lin_inc (d2v); d2var_typ_set (d2v, Some s2e)
end

implement d2var_typ_reset_at (d2v, s2e, s2l) = let
  val s2e = s2exp_whnf s2e
  val os2e_at = (
    case+ s2e.s2exp_node of
    | S2Eout _ => None ()
    | _ when s2cstref_exp_equ (Void_t0ype, s2e) => None ()
    | _ => Some (s2exp_at_viewt0ype_addr_view (s2e, s2l))
  ) : s2expopt
in
  d2var_lin_inc (d2v); d2var_typ_set (d2v, os2e_at)
end

implement d2var_ptr_viewat_make (d2v_ptr, od2v_view) = let
  val loc = d2var_loc_get d2v_ptr and sym = d2var_sym_get d2v_ptr
  val d2v_view = (case+ od2v_view of
    | D2VAROPTsome d2v_view => d2v_view | D2VAROPTnone () => let
       val sym_view = $Sym.symbol_make_string ($Sym.symbol_name sym + ".view")
     in
       d2var_make (loc, sym_view)
     end // end of [D2VAROPTnone]
  ) : d2var_t
  val () = d2var_lin_set (d2v_view, 0)
  val () = d2var_addr_set (d2v_view, d2var_addr_get d2v_ptr)
in
  d2v_view
end // end of [d2var_ptr_viewat_make]

implement d2var_ptr_viewat_make_none (d2v_ptr) =
  d2var_ptr_viewat_make (d2v_ptr, D2VAROPTnone ())
// end of [d2var_ptr_viewat_make_none]

(* ****** ****** *)

// implementing [d2varset_t]

local

staload Set = "ats_set_fun.sats"
staload _(*anonymous*) = "ats_set_fun.dats"

assume d2varset_t = $Set.set_t (d2var_t)

fn cmp (d2v1: d2var_t, d2v2: d2var_t):<fun> Sgn =
  $effmask_all (compare (d2v1, d2v2))

fn fprint_d2varset_ptr {m:file_mode} {l:addr} (
    pf_mod: file_mode_lte (m, w)
  , pf_out: !FILE m @ l
  | p: ptr l
  , dvs: d2varset_t
  ) : void = let

  typedef ptrint = (ptr l, int)

  var pi: ptrint; val () = pi.0 := p; val () = pi.1 := 0

  viewdef V = @(FILE m @ l, ptrint @ pi)

  fn pr (pf: !V | d2v: d2var_t, pi: !ptr pi): void = let
    prval pf_out = pf.0
    prval pf_at = pf.1; val p = pi->0; val i = pi->1
  in
    if i > 0 then fprint1_string (pf_mod | !p, ", ");
    pi->1 := i + 1;
    fprint_d2var (pf_mod | !p, d2v);
    pf.0 := pf_out; pf.1 := pf_at;
  end // end of [pr]

  prval pf = (pf_out, view@ pi)

  val () = $Set.set_foreach_main {V} {ptr pi} (pf | dvs, pr, &pi)

in // in of [let]

  pf_out := pf.0; view@ pi := pf.1

end // end of [fprint_d2varset_ptr]

in // in of [local]

implement fprint_d2varset (pf | out, dvs) = 
  fprint_d2varset_ptr (pf, view@ out | &out, dvs)

implement d2varset_nil = $Set.set_nil

implement d2varset_add (dvs, d2v) = $Set.set_insert (dvs, d2v, cmp)
implement d2varset_adds (dvs, d2vs) = case+ d2vs of
  | list_cons (d2v, d2vs) => d2varset_adds (d2varset_add (dvs, d2v), d2vs)
  | list_nil () => dvs
// end of [d2varset_adds]

implement d2varset_del (dvs, d2v) = $Set.set_remove (dvs, d2v, cmp)
implement d2varset_dels (dvs, d2vs) = case+ d2vs of
  | list_cons (d2v, d2vs) => d2varset_dels (d2varset_del (dvs, d2v), d2vs)
  | list_nil () => dvs
// end of [d2varset_dels]

implement d2varset_union (dvs1, dvs2) = $Set.set_union (dvs1, dvs2, cmp)

implement d2varset_ismem (dvs, d2v) = $Set.set_member (dvs, d2v, cmp)

implement d2varset_foreach_main (pf | dvs, f, env) = begin
  $Set.set_foreach_main (pf | dvs, f, env)
end // end of [d2varset_foreach_main]

implement d2varset_foreach_cloptr (dvs, f) = begin
  $Set.set_foreach_cloptr (dvs, f)
end // end of [d2varset_foreach_cloptr]

end // end of [local]

implement print_d2varset (dvs) = print_mac (fprint_d2varset, dvs)
implement prerr_d2varset (dvs) = prerr_mac (fprint_d2varset, dvs)

(* ****** ****** *)

(* end of [ats_dynexp2_dvar.dats] *)
