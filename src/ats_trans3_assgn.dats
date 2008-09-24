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

(* Mainly for handling assignments during type-checking *)

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Lst = "ats_list.sats"
staload SOL = "ats_staexp2_solve.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_stadyncst2.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_trans3.sats"

(* ****** ****** *)

overload prerr with $Loc.prerr_location

(* ****** ****** *)

implement s2exp_addr_slablst_assgn (loc0, s2e0, s2ls0, s2e_new) = let
  val @(s2r0, s2ls0_ft) = s2exp_addr_normalize s2e0
  val s2ls0 = $Lst.list_append (s2ls0_ft, s2ls0)
in
  case+ the_d2varset_env_find_viewat (s2r0, s2ls0) of
  | ~Some_vt ans => let
      val @(d2v_view, s2e_vt, s2e_addr, s2ls_ft, s2ls_bk) = ans
      val _ (* is_local_llam *) =
        the_d2varset_env_d2var_is_llam_local d2v_view
      var cstr: s2explst = list_nil ()
      val (s2e_old, s2e_vt, s2ls_bk) = begin
        s2exp_slablst_linset_cstr (loc0, s2e_vt, s2ls_bk, s2e_new, cstr)
      end
      val () = trans3_env_add_proplst (loc0, cstr)
(*
      val () = begin
        print "s2exp_addr_slablst_assgn: d2v_view = "; print d2v_view; print_newline ();
        print "s2exp_addr_slablst_assgn: s2e_vt = "; print s2e_vt; print_newline ();
        print "s2exp_addr_slablst_assgn: s2e_addr = "; print s2e_addr; print_newline ();
      end
*)
      val s2ls0_bk = s2lablst_trim_s2lablst_s2lablst (s2ls0_ft, s2ls_ft, s2ls_bk)
      var err: int = 0
      val () = $SOL.s2exp_size_equal_solve_err (loc0, s2e_new, s2e_old, err)
      val () = // error checking
        if err > 0 then begin
          prerr loc0;
          prerr ": error(3)";
          prerr ": size mismatch for assignment";
          prerr ": the following two types are expected to be size-equal but they may not be:";
          prerr_newline ();
          prerr s2e_new;
          prerr_newline ();
          prerr s2e_old;
          prerr_newline ();
          $Err.abort ()
        end
      val () = d2var_typ_reset_at (d2v_view, s2e_vt, s2e_addr)
      val () = // linearity checking
        if s2exp_is_linear s2e_old then begin
          prerr loc0;
          prerr ": error(3)";
          prerr ": a linear value of the type [";
          prerr s2e_old;
          prerr "] is abandoned.";
          prerr_newline ();
          $Err.abort {void} ()
        end
    in
      s2ls0_bk
    end
  | ~None_vt () => let
      fun aux (s2ls: s2lablst): void = begin case+ s2ls of
        | list_cons (s2l, s2ls) => (prerr "."; prerr s2l; aux s2ls)
        | list_nil () => ()
      end // end of [aux]
    in
      prerr loc0;
      prerr ": error(3)";
      prerr ": there is no view at [";
      prerr s2r0; aux s2ls0; prerr "]";
      prerr_newline ();
      $Err.abort {s2lablst} ()
    end
end // end of [s2exp_addr_slablst_assgn]

(* ****** ****** *)

implement d2var_lin_slablst_assgn (loc0, d2v, s2ls, s2e_new) = let
(*
  val () = begin
    print "d2var_lin_slablst_assgn: d2v = "; print d2v; print_newline ()
  end
*)
  val s2e0: s2exp = case+ d2var_typ_get d2v of
    | Some s2e => s2e | None () => s2exp_void_t0ype ()
(*
  val () = begin
    print "d2var_lin_slablst_assgn: s2e0 = "; print s2e0; print_newline ()
  end
*)
  var cstr: s2explst = list_nil ()
  val (s2e_old, s2e0, s2ls) = begin
    s2exp_slablst_linset_cstr (loc0, s2e0, s2ls, s2e_new, cstr)
  end
(*
  val () = begin
    print "d2var_lin_slablst_assgn: s2e0 = "; print s2e0; print_newline ()
  end
*)
  val () = trans3_env_add_proplst (loc0, cstr)
  val () = // linearity checking
    if s2exp_is_linear s2e_old then begin
      prerr loc0;
      prerr ": error(3)";
      prerr ": a linear value of the type [";
      prerr s2e_old;
      prerr "] is abandoned.";
      prerr_newline ();
      $Err.abort {void} ()
    end
in
  d2var_lin_inc (d2v); d2var_typ_set (d2v, Some s2e0); s2ls
end

(* ****** ****** *)

implement d2var_mut_slablst_assgn (loc0, d2v, s2ls, s2e_new) = let
  val s2e_addr = case+ d2var_addr_get d2v of
    | Some s2e => s2e
    | None () => begin
        prerr loc0;
        prerr ": error(3)";
        prerr ": the dynamic variable ["; prerr d2v;
        prerr "] is expected to be mutable but it is not.";
        prerr_newline ();
        $Err.abort {s2exp} ()
      end
in
  s2exp_addr_slablst_assgn (loc0, s2e_addr, s2ls, s2e_new)
end

(* ****** ****** *)

(* end of [ats_trans3_assgn.dats] *)
