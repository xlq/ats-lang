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

// Time: March 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload Cnt = "ats_counter.sats"
staload Err = "ats_error.sats"
staload IntInf = "ats_intinf.sats"
staload Lab = "ats_label.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

staload "ats_hiexp.sats"
staload "ats_ccomp.sats"

(* ****** ****** *)

implement print_tmplab (tl) = print_mac (fprint_tmplab, tl)
implement prerr_tmplab (tl) = prerr_mac (fprint_tmplab, tl)

(* ****** ****** *)

implement print_tmpvar (tmp) = print_mac (fprint_tmpvar, tmp)
implement prerr_tmpvar (tmp) = prerr_mac (fprint_tmpvar, tmp)

implement fprint_tmpvarlst {m} (pf | out, tmps) = let
  fun aux (out: &FILE m, i: int, tmps: tmpvarlst): void =
    case+ tmps of
    | list_cons (tmp, tmps) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_tmpvar (pf | out, tmp); aux (out, i+1, tmps)
      end
    | list_nil () => ()
in
  aux (out, 0, tmps)
end // end of [fprint_tmpvarlst]

implement print_tmpvarlst (tmps) = print_mac (fprint_tmpvarlst, tmps)
implement prerr_tmpvarlst (tmps) = prerr_mac (fprint_tmpvarlst, tmps)

(* ****** ****** *)

implement print_funlab (fl) = print_mac (fprint_funlab, fl)
implement prerr_funlab (fl) = prerr_mac (fprint_funlab, fl)

(* ****** ****** *)

implement fprint_funlablst {m} (pf | out, fls) = let
  fun aux (out: &FILE m, i: int, fls: funlablst): void =
    case+ fls of
    | list_cons (fl, fls) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_funlab (pf | out, fl); aux (out, i+1, fls)
      end
    | list_nil () => ()
in
  aux (out, 0, fls)
end // end of [fprint_funlablst]

implement print_funlablst (fls) = print_mac (fprint_funlablst, fls)
implement prerr_funlablst (fls) = prerr_mac (fprint_funlablst, fls)

(* ****** ****** *)

implement fprint_valprim (pf | out, vp) = begin
  case+ vp.valprim_node of
  | VParg i => begin
      fprint (pf | out, "VParg(");
      fprint_int (pf | out, i);
      fprint (pf | out, ")")
    end // end of [VParg]
  | VParg_ref i => begin
      fprint (pf | out, "VParg_ref(");
      fprint_int (pf | out, i);
      fprint (pf | out, ")")
    end // end of [VParg_ref]
  | VPbool b => begin
      fprint (pf | out, "VPbool(");
      fprint (pf | out, b);
      fprint (pf | out, ")")
    end // end of [VPbool]
  | VPchar c => begin
      fprint (pf | out, "VPchar(");
      fprint (pf | out, c);
      fprint (pf | out, ")")
    end // end of [VPchar]
  | VPclo (knd, fl, ctx) => begin
      fprint (pf | out, "VPclo(");
      fprint_int (pf | out, knd);
      fprint (pf | out, "; ");
      fprint_funlab (pf | out, fl);
      fprint (pf | out, "; ");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | VPcst (d2c) => begin
      fprint (pf | out, "VPcst(");
      fprint (pf | out, d2c);
      fprint (pf | out, ")")
    end // end of [VPcst]
  | VPenv vtp => begin
      fprint (pf | out, "VPenv(");
      fprint_vartyp (pf | out, vtp);
      fprint (pf | out, ")")
    end
  | VPext code => begin
      fprintf (pf | out, "VPext(\"%s\")", @(code));
    end 
  | VPfloat f(*string*) => begin
      fprintf (pf | out, "VPfloat(%s)", @(f))
    end
  | VPfun fl => begin
      fprint (pf | out, "VPfun(");
      fprint_funlab (pf | out, fl);
      fprint (pf | out, ")")
    end
  | VPint (int) => begin
      fprint (pf | out, "VPint(");
      $IntInf.fprint_intinf (pf | out, int);
      fprint (pf | out, ")")
    end
  | VPintsp (str, int) => begin
      fprintf (pf | out, "VPintsp(%s)", @(str))
    end
  | VPptrof vp => begin
      fprint (pf | out, "VPptrof(");
      fprint_valprim (pf | out, vp);
      fprint (pf | out, ")")
    end
  | VPptrof_ptr_offs (vp, offs) => begin
      fprint (pf | out, "VPptrof_ptr_offs(");
      fprint_valprim (pf | out, vp);
      fprint (pf | out, "; ");
      fprint_offsetlst (pf | out, offs);
      fprint (pf | out, ")")
    end
  | VPptrof_var_offs (vp, offs) => begin
      fprint (pf | out, "VPptrof_var_offs(");
      fprint_valprim (pf | out, vp);
      fprint (pf | out, "; ");
      fprint_offsetlst (pf | out, offs);
      fprint (pf | out, ")")
    end
  | VPsizeof hit => begin
      fprint (pf | out, "VPsizeof(");
      fprint_hityp (pf | out, hityp_decode hit);
      fprint (pf | out, ")")
    end
  | VPstring (str, len) => begin
      fprint (pf | out, "VPstring(...)")
    end
  | VPtmp tmp => begin
      fprint (pf | out, "VPtmp(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, ")")
    end
  | VPtmp_ref tmp => begin
      fprint (pf | out, "VPtmp_ref(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, ")")
    end
  | VPtop () => begin
      fprint (pf | out, "VPtop()")
    end
  | VPvoid () => begin
      fprint (pf | out, "VPvoid()")
    end
(*
  | _ => begin
      fprint (pf | out, "fprint_valprim: not yet implemented.");
      fprint_newline (pf | out);
      $Err.abort {void} ()
    end
*)
end // end of [fprint_valprim]

(* ****** ****** *)

implement fprint_valprimlst {m} (pf | out, vps) = let
  fun aux (out: &FILE m, i: int, vps: valprimlst): void =
    case+ vps of
    | list_cons (vp, vps) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_valprim (pf | out, vp); aux (out, i+1, vps)
      end
    | list_nil () => ()
in
  aux (out, 0, vps)
end // end of [fprint_valprimlst]

implement fprint_labvalprimlst {m} (pf | out, lvps) = let
  fun aux (out: &FILE m, i: int, lvps: labvalprimlst): void =
    case+ lvps of
    | LABVALPRIMLSTcons (l, vp, lvps) => begin
        if i > 0 then fprint (pf | out, ", ");
        $Lab.fprint_label (pf | out, l); fprint (pf | out, "= ");
        fprint_valprim (pf | out, vp); aux (out, i+1, lvps)
      end
    | LABVALPRIMLSTnil () => ()
in
  aux (out, 0, lvps)
end // end of [fprint_labvalprimlst]

(* ****** ****** *)

implement fprint_offset {m} (pf | out, off) = begin
  case+ off of
  | OFFSETlab (l, _(*hit_rec*)) => begin
      fprint (pf | out, "."); $Lab.fprint_label (pf | out, l)
    end
  | OFFSETind (vpss, _(*hit_elt*)) => aux (out, vpss) where {
      fun aux (out: &FILE m, vpss: valprimlstlst)
        : void = begin case+ vpss of
        | list_cons (vps, vpss) => begin
            fprint (pf | out, "[");
            fprint_valprimlst (pf | out, vps);
            fprint (pf | out, "]");
            aux (out, vpss)
          end
        | list_nil () => ()
      end // end of [aux]
    } // end of [where]
end // end of [fprint_offset]

implement fprint_offsetlst {m} (pf | out, offs) = let
  fun aux (out: &FILE m, i: int, offs: offsetlst): void =
    case+ offs of
    | list_cons (off, offs) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_offset (pf | out, off); aux (out, i+1, offs)
      end
    | list_nil () => ()
in
  aux (out, 0, offs)
end // end of [fprint_offsetlst]

(* ****** ****** *)

implement fprint_patck (pf | out, patck) = begin
  case+ patck of
  | PATCKbool b => begin
      fprint (pf | out, "PATCKbool(");
      fprint (pf | out, b);
      fprint (pf | out, ")")
    end
  | PATCKchar c => begin
      fprint (pf | out, "PATCKchar(");
      fprint (pf | out, c);
      fprint (pf | out, ")")
    end
  | PATCKcon d2c => begin
      fprint (pf | out, "PATCKcon(");
      fprint_d2con (pf | out, d2c);
      fprint (pf | out, ")")
    end
  | PATCKexn d2c => begin
      fprint (pf | out, "PATCKexn(");
      fprint_d2con (pf | out, d2c);
      fprint (pf | out, ")")
    end
  | PATCKfloat f(*string*) => begin
      fprint (pf | out, "PATCKfloat(");
      fprint (pf | out, f);
      fprint (pf | out, ")")
    end
  | PATCKint i => begin
      fprint (pf | out, "PATCKint(");
      $IntInf.fprint_intinf (pf | out, i);
      fprint (pf | out, ")")
    end
  | PATCKstring s => begin
      fprintf (pf | out, "PATCKstring(\"%s\")", @(s))
    end
end

implement fprint_patcklst {m} (pf | out, patcks) = let
  fun aux (out: &FILE m, i: int, patcks: patcklst): void =
    case+ patcks of
    | list_cons (patck, patcks) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_patck (pf | out, patck); aux (out, i+1, patcks)
      end
    | list_nil () => ()
in
  aux (out, 0, patcks)
end // end of [fprint_patcklst]

(* ****** ****** *)

implement fprint_kont {m} (pf | out, k) = begin
  case+ k of
  | KONTtmplab tl => begin
      fprint (pf | out, "KONTtmplab(");
      fprint_tmplab (pf | out, tl);
      fprint (pf | out, ")")
    end
  | KONTtmplabint (tl, i) => begin
      fprint (pf | out, "KONTtmplabint(");
      fprint_tmplab (pf | out, tl);
      fprint (pf | out, ", ");
      fprint_int (pf | out, i);
      fprint (pf | out, ")")
    end
  | KONTcaseof_fail () => begin
      fprint (pf | out, "KONTcaseof_fail()")
    end
  | KONTfunarg_fail fl => begin
      fprint (pf | out, "KONTfunarg_fail(");
      fprint_funlab (pf | out, fl);
      fprint (pf | out, ")")
    end
  | KONTmatpnt mpt => begin
      fprint (pf | out, "KONTmatpnt(...)")
    end
  | KONTraise vp => begin
      fprint (pf | out, "KONTraise(");
      fprint_valprim (pf | out, vp);
      fprint (pf | out, ")")
    end
  | KONTnone () => begin
      fprint (pf | out, "KONTnone()")
    end
end // end of [fprint_kont]

implement fprint_kontlst {m} (pf | out, ks) = let
  fun aux (out: &FILE m, i: int, ks: kontlst): void =
    case+ ks of
    | list_cons (k, ks) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_kont (pf | out, k); aux (out, i+1, ks)
      end
    | list_nil () => ()
in
  aux (out, 0, ks)
end // end of [fprint_kontlst]

(* ****** ****** *)

implement fprint_instr (pf | out, ins) = begin
  case+ ins of
  | INSTRarr (tmp, arrsz, hit_elt) => begin
      fprint (pf | out, "INSTRarr(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, "; ");
      fprint_int (pf | out, arrsz);
      fprint (pf | out, "; ");
      fprint_hityp (pf | out, hityp_decode hit_elt);
      fprint (pf | out, ")");
    end
  | INSTRcall (tmp, hit_fun, vp_fun, vps_arg) => begin
      fprint (pf | out, "INSTRcall(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, "; ");
      fprint_hityp (pf | out, hityp_decode hit_fun);
      fprint (pf | out, "; ");
      fprint_valprim (pf | out, vp_fun);
      fprint (pf | out, "; ");
      fprint_valprimlst (pf | out, vps_arg);
      fprint (pf | out, ")")
    end
  | INSTRcall_tail (fl) => begin
      fprint (pf | out, "INSTRcall_tail(");
      fprint_funlab (pf | out, fl);
      fprint (pf | out, ")")
    end
  | INSTRcond (vp, inss1, inss2) => begin
      fprint (pf | out, "INSTRcond(");
      fprint_valprim (pf | out, vp);
      fprint_newline (pf | out);
      fprint (pf | out, "INSTRcond_then:");
      fprint_newline (pf | out);
      fprint_instrlst (pf | out, inss1);
      fprint_newline (pf | out);
      fprint (pf | out, "INSTRcond_else:");
      fprint_newline (pf | out);
      fprint_instrlst (pf | out, inss2);
      fprint_newline (pf | out);
      fprint (pf | out, ")")
    end
  | INSTRdefine_clo (d2c, fl) => begin
      fprint (pf | out, "INSTRdefine_clo(");
      fprint_d2cst (pf | out, d2c);
      fprint (pf | out, ", ");
      fprint_funlab (pf | out, fl);
      fprint (pf | out, ")")
    end
  | INSTRdefine_fun (d2c, fl) => begin
      fprint (pf | out, "INSTRdefine_fun(");
      fprint_d2cst (pf | out, d2c);
      fprint (pf | out, ", ");
      fprint_funlab (pf | out, fl);
      fprint (pf | out, ")")
    end
  | INSTRdefine_val (d2c, vp) => begin
      fprint (pf | out, "INSTRdefine_val(");
      fprint_d2cst (pf | out, d2c);
      fprint (pf | out, ", ");
      fprint_valprim (pf | out, vp);
      fprint (pf | out, ")")
    end
  | INSTRextern cmd => begin
      fprintf (pf | out, "INSTRextern(\"%s\")", @(cmd))
    end
  | INSTRextval (name, vp) => begin
      fprint (pf | out, "INSTRextval(");
      fprint_string (pf | out, name);
      fprint (pf | out, ", ");
      fprint_valprim (pf | out, vp);
      fprint (pf | out, ")")
    end
  | INSTRfreeptr vp => begin
      fprint (pf | out, "INSTRfreeptr(");
      fprint_valprim (pf | out, vp);
      fprint (pf | out, ")")
    end
  | INSTRfunction _ => begin
      fprint (pf | out, "INSTRfunction(...)")
    end
  | INSTRfunlab fl => begin
      fprint (pf | out, "INSTRfunlab(");
      fprint_funlab (pf | out, fl);
      fprint (pf | out, ")")
    end
  | INSTRdynload_file (fil) => begin
      fprint (pf | out, "INSTRdynload_file(");
      $Fil.fprint_filename (pf | out, fil);
      fprint (pf | out, ")")
    end
  | INSTRload_ptr (tmp, vp_ptr) => begin
      fprint (pf | out, "INSTRload_ptr(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, "; ");
      fprint_valprim (pf | out, vp_ptr);
      fprint (pf | out, ")")
    end
  | INSTRload_ptr_offs (tmp, vp_ptr, offs) => begin
      fprint (pf | out, "INSTRload_ptr_offs(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, "; ");
      fprint_valprim (pf | out, vp_ptr);
      fprint (pf | out, "; ");
      fprint_offsetlst (pf | out, offs);
      fprint (pf | out, ")")
    end
  | INSTRload_var (tmp, vp_var) => begin
      fprint (pf | out, "INSTRload_var(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, "; ");
      fprint_valprim (pf | out, vp_var);
      fprint (pf | out, ")")
    end
  | INSTRload_var_offs (tmp, vp_var, offs) => begin
      fprint (pf | out, "INSTRload_var_offs(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, "; ");
      fprint_valprim (pf | out, vp_var);
      fprint (pf | out, "; ");
      fprint_offsetlst (pf | out, offs);
      fprint (pf | out, ")")
    end
  | INSTRloop _ => begin
      fprint (pf | out, "INSTRloop(...)")
    end
  | INSTRloopexn (knd, tl) => begin
      fprint (pf | out, "INSTRloopexn(");
      fprint_int (pf | out, knd);
      fprint (pf | out, "; ");
      fprint_tmplab (pf | out, tl);
      fprint (pf | out, ")")
    end
  | INSTRmove_arg (arg, vp) => begin
      fprint (pf | out, "INSTRmove_arg(");
      fprint_int (pf | out, arg);
      fprint (pf | out, ", ");
      fprint_valprim (pf | out, vp);
      fprint (pf | out, ")")
    end
  | INSTRmove_con (tmp, hit_sum, d2c, vps_arg) => begin
      fprint (pf | out, "INSTRmove_con(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, "; ");
      fprint_hityp (pf | out, hityp_decode hit_sum);      
      fprint (pf | out, "; ");
      fprint_d2con (pf | out, d2c);
      fprint (pf | out, "; ");
      fprint_valprimlst (pf | out, vps_arg);
      fprint (pf | out, ")")
    end
  | INSTRmove_rec_box (tmp, hit_rec, lvps) => begin
      fprint (pf | out, "INSTRmove_rec_box(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, "; ");
      fprint_hityp (pf | out, hityp_decode hit_rec);
      fprint (pf | out, "; ");
      fprint_labvalprimlst (pf | out, lvps);
      fprint (pf | out, ")")
    end
  | INSTRmove_rec_flt (tmp, hit_rec, lvps) => begin
      fprint (pf | out, "INSTRmove_rec_flt(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, "; ");
      fprint_hityp (pf | out, hityp_decode hit_rec);
      fprint (pf | out, "; ");
      fprint_labvalprimlst (pf | out, lvps);
      fprint (pf | out, ")")
    end
  | INSTRmove_val (tmp, vp) => begin
      fprint (pf | out, "INSTRmove_val(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, "; ");
      fprint_valprim (pf | out, vp);
      fprint (pf | out, ")")
    end
  | INSTRmove_ref (tmp, vp) => begin
      fprint (pf | out, "INSTRmove_ref(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, "; ");
      fprint_valprim (pf | out, vp);
      fprint (pf | out, ")")
    end
  | INSTRpar_spawn (tmp_ret, vp_fun) => begin
      fprint (pf | out, "INSTRpar_spawn(");
      fprint_tmpvar (pf | out, tmp_ret);
      fprint (pf | out, "; ");
      fprint_valprim (pf | out, vp_fun);
      fprint (pf | out, ")")
    end
  | INSTRpar_synch (tmp_ret) => begin
      fprint (pf | out, "INSTRpar_synch(");
      fprint_tmpvar (pf | out, tmp_ret);
      fprint (pf | out, ")")
    end
  | INSTRpatck (vp, patck, k_fail) => begin
      fprint (pf | out, "INSTRpatck(");
      fprint_valprim (pf | out, vp);
      fprint (pf | out, "; ");
      fprint_patck (pf | out, patck);
      fprint (pf | out, "; ");
      fprint_kont (pf | out, k_fail);
      fprint (pf | out, ")")
    end
  | INSTRraise vp => begin
      fprint (pf | out, "INSTRraise(");
      fprint_valprim (pf | out, vp);
      fprint (pf | out, ")")
    end
  | INSTRselcon (tmp, vp_sum, hit_sum, i) => begin
      fprint (pf | out, "INSTRselcon(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, "; ");
      fprint_valprim (pf | out, vp_sum);
      fprint (pf | out, "; ");
      fprint_hityp (pf | out, hityp_decode hit_sum);
      fprint (pf | out, "; ");
      fprint_int (pf | out, i);
      fprint (pf | out, ")")
    end
  | INSTRselcon_ptr (tmp, vp_sum, hit_sum, i) => begin
      fprint (pf | out, "INSTRselcon_ptr(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, "; ");
      fprint_valprim (pf | out, vp_sum);
      fprint (pf | out, "; ");
      fprint_hityp (pf | out, hityp_decode hit_sum);
      fprint (pf | out, "; ");
      fprint_int (pf | out, i);
      fprint (pf | out, ")")
    end
  | INSTRselect (tmp, vp_root, offs) => begin
      fprint (pf | out, "INSTRselect(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, "; ");
      fprint_valprim (pf | out, vp_root);
      fprint (pf | out, "; ");
      fprint_offsetlst (pf | out, offs);
      fprint (pf | out, ")")
    end
  | INSTRstore_ptr (vp_ptr, vp_val) => begin
      fprint (pf | out, "INSTRstore_ptr(");
      fprint_valprim (pf | out, vp_ptr);
      fprint (pf | out, "; ");
      fprint_valprim (pf | out, vp_val);
      fprint (pf | out, ")")
    end
  | INSTRstore_ptr_offs (vp_ptr, offs, vp_val) => begin
      fprint (pf | out, "INSTRstore_ptr_offs(");
      fprint_valprim (pf | out, vp_ptr);
      fprint (pf | out, "; ");
      fprint_offsetlst (pf | out, offs);
      fprint (pf | out, "; ");
      fprint_valprim (pf | out, vp_val);
      fprint (pf | out, ")")
    end
  | INSTRstore_var (vp_var, vp_val) => begin
      fprint (pf | out, "INSTRstore_var(");
      fprint_valprim (pf | out, vp_var);
      fprint (pf | out, "; ");
      fprint_valprim (pf | out, vp_val);
      fprint (pf | out, ")")
    end
  | INSTRstore_var_offs (vp_var, offs, vp_val) => begin
      fprint (pf | out, "INSTRstore_var_offs(");
      fprint_valprim (pf | out, vp_var);
      fprint (pf | out, "; ");
      fprint_offsetlst (pf | out, offs);
      fprint (pf | out, "; ");
      fprint_valprim (pf | out, vp_val);
      fprint (pf | out, ")")
    end
  | INSTRswitch _ => begin
      fprint (pf | out, "INSTRswitch(...)")
    end
  | INSTRtmplabint (tl, i) => begin
      fprint (pf | out, "INSTRtmplabint(");
      fprint_tmplab (pf | out, tl);
      fprint (pf | out, "_");
      fprint_int (pf | out, i);
      fprint (pf | out, ")")
    end
  | INSTRtrywith _ => begin
      fprint (pf | out, "INSTRtrywith(...)")
    end
  | INSTRvardec tmp => begin
      fprint (pf | out, "INSTRvardec(");
      fprint_tmpvar (pf | out, tmp);
      fprint (pf | out, ")")
    end
(*
  | _ => begin
      fprint (pf | out, "fprint_instr: not yet implemented.");
      fprint_newline (pf | out);
      $Err.abort {void} ()
    end
*)
end // end of [fprint_instr]

implement fprint_instrlst {m} (pf | out, inss) = let
  fun aux (out: &FILE m, inss: instrlst): void = begin
    case+ inss of
    | list_cons (ins, inss) => begin
        fprint_instr (pf | out, ins); fprint_newline (pf | out);
        aux (out, inss)
      end
    | list_nil () => ()
  end
in
  aux (out, inss)
end // end of [fprint_instrlst]

(* ****** ****** *)

implement fprint_branch {m} (pf | out, br) = begin
  fprint_tmplab (pf | out, br.branch_lab);
  fprint (pf | out, ": "); fprint_newline (pf | out);
  fprint_instrlst (pf | out, br.branch_inss);
end // end of [fprint_branch]

implement fprint_branchlst {m} (pf | out, brs) = let
  fun aux (out: &FILE m, brs: branchlst): void = begin
    case+ brs of
    | list_cons (br, brs) => begin
        fprint_branch (pf | out, br); aux (out, brs)
      end
    | list_nil () => ()
  end
in
  aux (out, brs)
end // end of [fprint_branchlst]

(* ****** ****** *)

implement print_valprim (vp) = print_mac (fprint_valprim, vp)
implement prerr_valprim (vp) = prerr_mac (fprint_valprim, vp)

implement print_valprimlst (vps) = print_mac (fprint_valprimlst, vps)
implement prerr_valprimlst (vps) = prerr_mac (fprint_valprimlst, vps)
        
(* ****** ****** *)

implement print_instr (ins) = print_mac (fprint_instr, ins)
implement prerr_instr (ins) = prerr_mac (fprint_instr, ins)

(* ****** ****** *)

implement print_instrlst (inss) = print_mac (fprint_instrlst, inss)
implement prerr_instrlst (inss) = prerr_mac (fprint_instrlst, inss)

(* ****** ****** *)

(* end of [ats_ccomp_print.dats] *)
