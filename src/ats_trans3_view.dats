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

staload Err = "ats_error.sats"
staload Lst = "ats_list.sats"
staload SOL = "ats_staexp2_solve.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_stadyncst2.sats"
staload "ats_dynexp3.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_trans3.sats"

(* ****** ****** *)

overload prerr with $Loc.prerr_location

(* ****** ****** *)

implement s2exp_addr_viewat_slablst_try (loc0, s2e0_addr, s2ls0) = let
  val (s2r0, s2ls0_ft) = s2exp_addr_normalize s2e0_addr
  val s2ls0 = $Lst.list_append (s2ls0_ft, s2ls0)
in
  case+ the_d2varset_env_find_viewat (s2r0, s2ls0) of
  | ~Some_vt ans => let
      val @(d2v_view, s2e_vt, s2e_addr, s2ls_ft, s2ls_bk_nt) = ans
      var cstr: s2explst = list_nil ()
      val s2ls_bk = s2exp_slablst_lintry_cstr (loc0, s2e_vt, s2ls_bk_nt, cstr)
      val () = trans3_env_add_proplst (loc0, cstr)
    in
      s2lablst_trim_s2lablst_s2lablst (s2ls0_ft, s2ls_ft, s2ls_bk)
    end // end of [Some_vt]
  | ~None_vt () => let
      fun aux (s2ls: s2lablst): void = case+ s2ls of
        | list_cons (s2l, s2ls) => (prerr "."; prerr s2l; aux s2ls)
        | list_nil () => ()
    in
      prerr loc0;
      prerr ": error(3)";
      prerr ": there is no view at ["; prerr s2r0; aux s2ls0; prerr "]";
      prerr_newline ();
      $Err.abort ()
    end // end of [None_vt]
  // end of [case]
end // end of [s2exp_addr_viewat_slablst_try]

(* ****** ****** *)

implement s2exp_addr_viewat_slablst_get (loc0, s2e0_addr, s2ls0) = let
  val (s2r0, s2ls0_ft) = s2exp_addr_normalize s2e0_addr
  val s2ls0 = $Lst.list_append (s2ls0_ft, s2ls0)
in
  case+ the_d2varset_env_find_viewat (s2r0, s2ls0) of
  | ~Some_vt ans => let
      val @(d2v_view, s2e_vt, s2e_addr, s2ls_ft, s2ls_bk_nt) = ans
      var cstr: s2explst = list_nil ()
      val (s2e_out, s2e_vt, s2ls_bk) = begin
        s2exp_slablst_lindel_cstr (loc0, s2e_vt, s2ls_bk_nt, cstr)
      end
      val () = trans3_env_add_proplst (loc0, cstr)
      val () = d2var_typ_reset_at (d2v_view, s2e_vt, s2e_addr)
      val s2ls0_bk = begin
        s2lablst_trim_s2lablst_s2lablst (s2ls0_ft, s2ls_ft, s2ls_bk)
      end
      val s2e_at = begin
        s2exp_at_viewt0ype_addr_view (s2e_out, s2exp_projlst (s2r0, s2ls0_bk))
      end
    in
      @(s2e_at, s2ls0_bk, d2v_view, s2ls_bk_nt)
    end // end of [Some_vt]
  | ~None_vt () => let
      fun aux (s2ls: s2lablst): void = case+ s2ls of
        | list_cons (s2l, s2ls) => (prerr "."; prerr s2l; aux s2ls)
        | list_nil () => ()
    in
      prerr loc0;
      prerr ": error(3)";
      prerr ": there is no view at ["; prerr s2r0; aux s2ls0; prerr "]";
      prerr_newline ();
      $Err.abort ()
    end // end of [None_vt]
  // end of [case]
end // end of [s2exp_addr_viewat_slablst_get]

(* ****** ****** *)

implement s2exp_addr_viewat_slablst_set
  (loc0, s2e0_addr, s2ls0, s2e_new_at) = let
  val @(s2e_new, s2e_new_addr): @(s2exp, s2exp) =
    case+ un_s2exp_at_viewt0ype_addr_view s2e_new_at of
    | ~Some_vt (s2ts2a) => s2ts2a
    | ~None_vt () => begin
        prerr loc0;
        prerr ": error(3)";
        prerr ": the view ["; prerr s2e_new_at;
        prerr "] is expected to be an @-view";
        prerr_newline ();
        $Err.abort ()
      end
  val (s2r0, s2ls0_ft) = s2exp_addr_normalize s2e0_addr
  val s2ls0 = $Lst.list_append (s2ls0_ft, s2ls0)
in
  case+ the_d2varset_env_find_viewat (s2r0, s2ls0) of
  | ~Some_vt ans => let
      val @(d2v_view, s2e, s2e_addr, s2ls_ft, s2ls_bk_nt) = ans
      val _(* is_local_llam *) =
        the_d2varset_env_d2var_is_llam_local (d2v_view)
      var cstr: s2explst = list_nil ()
      val @(s2e_old, s2e, s2ls_bk) = begin
        s2exp_slablst_linset_cstr (loc0, s2e, s2ls_bk_nt, s2e_new, cstr)
      end
      val () = trans3_env_add_proplst (loc0, cstr)
      val () = 
        if s2exp_syneq (s2e_addr, s2e_new_addr) then () else begin
          prerr loc0;
          prerr ": error(3)";
          prerr ": address mismatch for @-view assignment: [";
          prerr s2e_addr; prerr "] <> [";
          prerr_s2exp s2e_new_addr; prerr "].";
          prerr_newline ();
          $Err.abort {void} ()
        end
      val s2ls0_bk = begin
        s2lablst_trim_s2lablst_s2lablst (s2ls0_ft, s2ls_ft, s2ls_bk)
      end
      val () = d2var_typ_reset_at (d2v_view, s2e, s2e_addr)
      val () = $SOL.s2exp_out_void_solve (loc0, s2e_old)
    in
      s2ls0_bk
    end // end of [Some_vt]
  | ~None_vt () => begin
      prerr loc0;
      prerr ": error(3)";
      prerr ": the @-view associated with the location [";
      prerr s2r0; prerr "] cannot be found."; prerr_newline ();
      $Err.abort {s2lablst} ()
    end
end // end of [s2exp_addr_viewat_slablst_set]

(* ****** ****** *)

fn d2var_view_viewat_slablst_set_main
  (loc0: loc_t,
   d2v_view: d2var_t,
   s2e0: s2exp,
   s2e0_addr: s2exp,
   s2ls_view: s2lablst,
   s2e_new_at: s2exp)
  : @(s2exp(*old*), s2lablst) = let
  val s2e_new_at = s2exp_whnf s2e_new_at
  val @(s2e_new, s2e_new_addr): @(s2exp, s2exp) =
    case+ un_s2exp_at_viewt0ype_addr_view s2e_new_at of
    | ~Some_vt s2ts2a => s2ts2a
    | ~None_vt () => begin
        prerr loc0;
        prerr ": error(3)";
        prerr ": the view ["; prerr s2e_new_at;
        prerr "] is expected to be an @-view";
        prerr_newline ();
        $Err.abort {@(s2exp, s2exp)} ()
      end
  var cstr: s2explst = list_nil ()
  val @(s2e_old, s2e0, s2ls) =
    s2exp_slablst_linset_cstr (loc0, s2e0, s2ls_view, s2e_new, cstr)
  val s2e_addr = s2exp_projlst (s2e0_addr, s2ls)
  val () = trans3_env_add_proplst (loc0, cstr)
  val () = 
    if s2exp_syneq (s2e_addr, s2e_new_addr) then () else begin
      prerr loc0;
      prerr ": error(3)";
      prerr ": address mismatch for @-view restoration: [";
      prerr s2e_addr; prerr "] <> [";
      prerr_s2exp s2e_new_addr; prerr "].";
      prerr_newline ();
      $Err.abort {void} ()
    end
  val () = d2var_typ_reset_at (d2v_view, s2e0, s2e0_addr)
in
  (s2e_old, s2ls)
end // end [d2var_view_viewat_slablst_set_main]

fn d2var_view_viewat_slablst_set
  (loc0: loc_t, d2v_view: d2var_t, s2ls: s2lablst, s2e_new_at: s2exp)
  : (s2exp (*old*), s2lablst) = begin
  case+ d2var_typ_get d2v_view of
  | Some s2e_at => begin
    case+ un_s2exp_at_viewt0ype_addr_view s2e_at of
    | ~Some_vt s2ts2a => begin
        d2var_view_viewat_slablst_set_main
          (loc0, d2v_view, s2ts2a.0, s2ts2a.1, s2ls, s2e_new_at)
      end // end of [Some_vt]
    | ~None_vt () => begin
        prerr loc0;
        prerr ": error(3)";
        prerr ": the view of ["; prerr d2v_view;
        prerr "] is expected to be an @-view but it is [";
        prerr s2e_at; prerr "] instead.";
        prerr_newline ();
        $Err.abort ()
      end
    end // end [Some]
  | None () => let
      val s2e0 = s2exp_void_t0ype ()
      val s2e0_addr = d2var_addr_get_some (loc0, d2v_view)
    in
      d2var_view_viewat_slablst_set_main
        (loc0, d2v_view, s2e0, s2e0_addr, s2ls, s2e_new_at)
    end
end // end of [d2var_view_viewat_slablst_set]

(* ****** ****** *)

fun s2lab0lst_of_d3lab1lst {n:nat} .<n>.
  (d3ls: list (d3lab1, n)): list (s2lab, n) = case+ d3ls of
  | list_cons (d3l, d3ls) => let
      val s2l = case+ d3l.d3lab1_node of
        | D3LAB1ind (d3ess, _) => S2LAB0ind (d3explstlst_ind_get d3ess)
        | D3LAB1lab (l, _) => S2LAB0lab l
    in
      list_cons (s2l, s2lab0lst_of_d3lab1lst d3ls)
    end
  | list_nil () => list_nil ()

(* ****** ****** *)

implement d3exp_lval_typ_set (loc0, refval, d3e0, s2e_new, err) = let
(*
  val () = begin
    print "d3exp_lval_typ_set: d3e0 = "; print d3e0; print_newline ()
  end
*)
  fn refval_check (loc0: loc_t, d2v: d2var_t, refval: int): void = 
    if refval > 1 then begin
      prerr loc0;
      prerr ": error(3)";
      prerr ": the dynamic variable ["; prerr d2v;
      prerr "] is required to be mutable in order to support call-by-reference.";
      $Err.abort {void} ()
    end
in
  case+ d3e0.d3exp_node of
  | D3Eann_type (d3e, _(*s2e_ann*)) => begin
      d3exp_lval_typ_set (loc0, refval, d3e, s2e_new, err)
    end
  | D3Esel_ptr (d3e, d3ls) => begin
    case+ un_s2exp_ptr_addr_type d3e.d3exp_typ of
    | ~Some_vt s2e_addr => let
        val s2ls_nt = s2lab0lst_of_d3lab1lst d3ls
        val _(* s2lablst *) = begin
          s2exp_addr_slablst_assgn (loc0, s2e_addr, s2ls_nt, s2e_new)
        end
      in
        // empty
      end
    | ~None_vt () => begin
        prerr loc0;
        prerr ": Internal Error: d3exp_lval_typ_set: D3Esel_ptr";
        prerr_newline ();
        $Err.abort {void} ()
      end
    end // end of [D3Esel_ptr]
  | D3Esel_var (d2v, d3ls) when d2var_is_linear d2v => let
      val () = refval_check (loc0, d2v, refval)
      val s2ls_nt = s2lab0lst_of_d3lab1lst d3ls
      val _(* s2lablst *) = begin
        d2var_lin_slablst_assgn (loc0, d2v, s2ls_nt, s2e_new)
      end
    in
      // empty
    end
  | D3Esel_var (d2v, d3ls) when d2var_is_mutable d2v => let
      val s2ls_nt = s2lab0lst_of_d3lab1lst d3ls
      val _(* s2lablst *) = begin
        d2var_mut_slablst_assgn (loc0, d2v, s2ls_nt, s2e_new)
      end
    in
      // empty
    end
  | D3Evar d2v when d2var_is_linear d2v => let
      val () = refval_check (loc0, d2v, refval)
      val _(* nil *) = begin
        d2var_lin_slablst_assgn (loc0, d2v, list_nil (), s2e_new)
      end
    in
      // empty
    end
  | D3Evar d2v when d2var_is_mutable d2v => let
      val _ (* nil *) = begin
        d2var_mut_slablst_assgn (loc0, d2v, list_nil (), s2e_new)
      end
    in
      // empty
    end
  | D3Eviewat_ptr (d3e, d3ls, d2v_view, s2ls_nt) => let
      val (s2e_old, s2ls) = begin
        d2var_view_viewat_slablst_set (loc0, d2v_view, s2ls_nt, s2e_new)
      end
    in
      $SOL.s2exp_out_void_solve (loc0, s2e_old)
    end
  | D3Eviewat_var (d2v, d3ls, d2v_view, s2ls_nt) => let
      val (s2e_old, s2ls) = begin
        d2var_view_viewat_slablst_set (loc0, d2v_view, s2ls_nt, s2e_new)
      end
    in
      $SOL.s2exp_out_void_solve (loc0, s2e_old)
    end
  | _ => (err := err + 1)
  // end of [case]
end // end of [d3exp_lval_typ_set]

fn s2exp_fun_is_freeptr (s2e: s2exp): bool = begin case+ s2e.s2exp_node of
  | S2Efun (_(*fc*), lin, _(*s2fe*), _(*npf*), _(*arg*), _(*res*)) => begin
      if lin > 0 then false else true
    end
  | _ => false
end // end of [s2exp_fun_is_freeptr]

implement d3exp_lval_typ_set_arg (refval, d3e0, s2e_new) = let
  val loc0 = d3e0.d3exp_loc; var err: int = 0
  val flag = (
    if refval = 0 then
      (if s2exp_is_linear (d3e0.d3exp_typ) then 1 else 0)
    else 1
  ) : int
  val () =
    if flag > 0 then begin
      d3exp_lval_typ_set (loc0, refval, d3e0, s2e_new, err)
    end
in
  if err > 0 then begin case+ s2e_new of
    | _ when s2exp_fun_is_freeptr s2e_new => 1 (*freeknd*)
    | _ => begin
        prerr loc0;
        prerr ": error(3)";
        prerr ": the dynamic expression needs to be a left-value but it is not.";
        prerr_newline ();
        $Err.abort {int} ()
      end
  end else begin
    0 (*freeknd*)
  end
end // end of [d3exp_lval_typ_set_arg]

implement d3exp_lval_typ_set_pat (d3e0, p3t) = begin
  case+ p3t.p3at_typ_lft of
  | Some s2e => let
      val loc0 = d3e0.d3exp_loc; var err: int = 0
      val () = d3exp_lval_typ_set (loc0, 0(*val*), d3e0, s2e, err)
    in
      if err > 0 then begin
        prerr loc0;
        prerr ": error(3)";
        prerr ": the dynamic expression needs to be a left-value but it is not.";
        prerr_newline ();
        $Err.abort {void} ()
      end
    end
  | None () => ()
end // end of [d3exp_lval_typ_set_pat]

(* ****** ****** *)

(* end of [ats_trans3_view.dats] *)
