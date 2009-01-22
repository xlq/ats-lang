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

macdef fprint_label = $Lab.fprint_label

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
        if i > 0 then fprint1_string (pf | out, ", ");
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
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_funlab (pf | out, fl); aux (out, i+1, fls)
      end
    | list_nil () => ()
in
  aux (out, 0, fls)
end // end of [fprint_funlablst]

implement print_funlablst (fls) = print_mac (fprint_funlablst, fls)
implement prerr_funlablst (fls) = prerr_mac (fprint_funlablst, fls)

(* ****** ****** *)

implement fprint_valprim (pf | out, vp) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ vp.valprim_node of
  | VParg i => begin
      strpr "VParg("; fprint1_int (pf | out, i); strpr ")"
    end // end of [VParg]
  | VParg_ref i => begin
      strpr "VParg_ref("; fprint1_int (pf | out, i); strpr ")"
    end // end of [VParg_ref]
  | VPbool b => begin
      strpr "VPbool("; fprint1_bool (pf | out, b); strpr ")"
    end // end of [VPbool]
  | VPchar c => begin
      strpr "VPchar("; fprint1_char (pf | out, c); strpr ")"
    end // end of [VPchar]
  | VPclo (knd, fl, ctx) => begin
      strpr "VPclo(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_funlab (pf | out, fl);
      strpr "; ";
      fprint1_string (pf | out, "...");
      strpr ")"
    end
  | VPcst (d2c) => begin
      strpr "VPcst("; fprint_d2cst (pf | out, d2c); strpr ")"
    end // end of [VPcst]
  | VPenv vtp => begin
      strpr "VPenv("; fprint_vartyp (pf | out, vtp); strpr ")"
    end
  | VPext code => begin
      fprintf1_exn (pf | out, "VPext(\"%s\")", @(code));
    end 
  | VPfloat f(*string*) => begin
      fprintf1_exn (pf | out, "VPfloat(%s)", @(f))
    end
  | VPfun fl => begin
      strpr "VPfun(";
      fprint_funlab (pf | out, fl);
      strpr ")"
    end
  | VPint (int) => begin
      strpr "VPint(";
      $IntInf.fprint_intinf (pf | out, int);
      strpr ")"
    end
  | VPintsp (str, int) => begin
      fprintf1_exn (pf | out, "VPintsp(%s)", @(str))
    end
  | VPptrof vp => begin
      strpr "VPptrof(";
      fprint_valprim (pf | out, vp);
      strpr ")"
    end
  | VPptrof_ptr_offs (vp, offs) => begin
      strpr "VPptrof_ptr_offs(";
      fprint_valprim (pf | out, vp);
      strpr "; ";
      fprint_offsetlst (pf | out, offs);
      strpr ")"
    end
  | VPptrof_var_offs (vp, offs) => begin
      strpr "VPptrof_var_offs(";
      fprint_valprim (pf | out, vp);
      strpr "; ";
      fprint_offsetlst (pf | out, offs);
      strpr ")"
    end
  | VPsizeof hit => begin
      strpr "VPsizeof(";
      fprint_hityp (pf | out, hityp_decode hit);
      strpr ")"
    end
  | VPstring (str, len) => begin
      fprint1_string (pf | out, "VPstring(...)")
    end
  | VPtmp tmp => begin
      strpr "VPtmp("; fprint_tmpvar (pf | out, tmp); strpr ")"
    end
  | VPtmp_ref tmp => begin
      strpr "VPtmp_ref("; fprint_tmpvar (pf | out, tmp); strpr ")"
    end
  | VPtop () => begin
      fprint1_string (pf | out, "VPtop()")
    end
  | VPvoid () => begin
      fprint1_string (pf | out, "VPvoid()")
    end
(*
  | _ => begin
      fprint1_string (pf | out, "fprint_valprim: not yet implemented.");
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
        if i > 0 then fprint1_string (pf | out, ", ");
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
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_label (pf | out, l); fprint1_string (pf | out, "= ");
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
      fprint1_string (pf | out, "."); fprint_label (pf | out, l)
    end
  | OFFSETind (vpss, _(*hit_elt*)) => aux (out, vpss) where {
      fun aux (out: &FILE m, vpss: valprimlstlst)
        : void = begin case+ vpss of
        | list_cons (vps, vpss) => begin
            fprint1_string (pf | out, "[");
            fprint_valprimlst (pf | out, vps);
            fprint1_string (pf | out, "]");
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
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_offset (pf | out, off); aux (out, i+1, offs)
      end
    | list_nil () => ()
in
  aux (out, 0, offs)
end // end of [fprint_offsetlst]

(* ****** ****** *)

implement fprint_patck (pf | out, patck) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ patck of
  | PATCKbool b => begin
      strpr "PATCKbool("; fprint1_bool (pf | out, b); strpr ")"
    end
  | PATCKchar c => begin
      strpr "PATCKchar("; fprint1_char (pf | out, c); strpr ")"
    end
  | PATCKcon d2c => begin
      strpr "PATCKcon("; fprint_d2con (pf | out, d2c); strpr ")"
    end
  | PATCKexn d2c => begin
      strpr "PATCKexn("; fprint_d2con (pf | out, d2c); strpr ")"
    end
  | PATCKfloat f(*string*) => begin
      strpr "PATCKfloat("; fprint1_string (pf | out, f); strpr ")"
    end
  | PATCKint i => begin
      strpr "PATCKint(";
      $IntInf.fprint_intinf (pf | out, i);
      strpr ")"
    end
  | PATCKstring s => begin
      fprintf1_exn (pf | out, "PATCKstring(\"%s\")", @(s))
    end
end

implement fprint_patcklst {m} (pf | out, patcks) = let
  fun aux (out: &FILE m, i: int, patcks: patcklst): void =
    case+ patcks of
    | list_cons (patck, patcks) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_patck (pf | out, patck); aux (out, i+1, patcks)
      end
    | list_nil () => ()
in
  aux (out, 0, patcks)
end // end of [fprint_patcklst]

(* ****** ****** *)

implement fprint_kont {m} (pf | out, k) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ k of
  | KONTtmplab tl => begin
      strpr "KONTtmplab(";
      fprint_tmplab (pf | out, tl);
      strpr ")"
    end // end of [KONTtmplab]
  | KONTtmplabint (tl, i) => begin
      strpr "KONTtmplabint(";
      fprint_tmplab (pf | out, tl);
      strpr ", ";
      fprint1_int (pf | out, i);
      strpr ")"
    end // end of [KONTtmplabint]
  | KONTcaseof_fail () => begin
      fprint1_string (pf | out, "KONTcaseof_fail()")
    end
  | KONTfunarg_fail fl => begin
      strpr "KONTfunarg_fail("; fprint_funlab (pf | out, fl); strpr ")"
    end
  | KONTmatpnt mpt => begin
      fprint1_string (pf | out, "KONTmatpnt(...)")
    end
  | KONTraise vp => begin
      strpr "KONTraise("; fprint_valprim (pf | out, vp); strpr ")"
    end
  | KONTnone () => begin
      fprint1_string (pf | out, "KONTnone()")
    end
end // end of [fprint_kont]

implement fprint_kontlst {m} (pf | out, ks) = let
  fun aux (out: &FILE m, i: int, ks: kontlst): void =
    case+ ks of
    | list_cons (k, ks) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_kont (pf | out, k); aux (out, i+1, ks)
      end
    | list_nil () => ()
in
  aux (out, 0, ks)
end // end of [fprint_kontlst]

(* ****** ****** *)

implement fprint_instr (pf | out, ins) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ ins of
  | INSTRarr_heap (tmp, asz, hit_elt) => begin
      strpr "INSTRarr_heap(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_int (pf | out, asz);
      strpr "; ";
      fprint_hityp (pf | out, hityp_decode hit_elt);
      strpr ")";
    end // end of [INSTRarr_heap]
  | INSTRarr_stack (tmp, vp_asz, hit_elt) => begin
      strpr "INSTRarr_stack(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_valprim (pf | out, vp_asz);
      strpr "; ";
      fprint_hityp (pf | out, hityp_decode hit_elt);
      strpr ")";
    end // end of [INSTRarr_stack]
  | INSTRassgn_arr (vp_arr, vp_asz, tmp_elt, vp_tsz) => begin
      strpr "INSTRassgn_arr(";
      fprint_valprim (pf | out, vp_arr);
      strpr "; ";
      fprint_valprim (pf | out, vp_asz);
      strpr "; ";
      fprint_tmpvar (pf | out, tmp_elt);
      strpr "; ";
      fprint_valprim (pf | out, vp_tsz);
      strpr ")";
    end // end of [INSTRassgn_arr]
  | INSTRassgn_clo (vp_clo, fl, env) => begin
      strpr "INSTRassgn_clo(";
      fprint_valprim (pf | out, vp_clo);
      strpr "; ";
      fprint_funlab (pf | out, fl);
      strpr "; ";
      fprint1_string (pf | out, "...");
      strpr ")";
    end // end of [INSTRassgn_clo]
  | INSTRcall (tmp, hit_fun, vp_fun, vps_arg) => begin
      strpr "INSTRcall(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_hityp (pf | out, hityp_decode hit_fun);
      strpr "; ";
      fprint_valprim (pf | out, vp_fun);
      strpr "; ";
      fprint_valprimlst (pf | out, vps_arg);
      strpr ")"
    end // end of [INSTRcall]
  | INSTRcall_tail (fl) => begin
      strpr "INSTRcall_tail("; fprint_funlab (pf | out, fl); strpr ")"
    end // end of [INSTRcall_tail]
  | INSTRcond (vp, inss1, inss2) => begin
      strpr "INSTRcond(";
      fprint_valprim (pf | out, vp);
      fprint_newline (pf | out);
      strpr "INSTRcond_then:";
      fprint_newline (pf | out);
      fprint_instrlst (pf | out, inss1);
      fprint_newline (pf | out);
      strpr "INSTRcond_else:";
      fprint_newline (pf | out);
      fprint_instrlst (pf | out, inss2);
      fprint_newline (pf | out);
      strpr ")"
    end // end of [INSTRcond]
  | INSTRdefine_clo (d2c, fl) => begin
      strpr "INSTRdefine_clo(";
      fprint_d2cst (pf | out, d2c);
      strpr ", ";
      fprint_funlab (pf | out, fl);
      strpr ")"
    end // end of [INSTRdefine_clo]
  | INSTRdefine_fun (d2c, fl) => begin
      strpr "INSTRdefine_fun(";
      fprint_d2cst (pf | out, d2c);
      strpr ", ";
      fprint_funlab (pf | out, fl);
      strpr ")"
    end // end of [INSTRdefine_fun]
  | INSTRdefine_val (d2c, vp) => begin
      strpr "INSTRdefine_val(";
      fprint_d2cst (pf | out, d2c);
      strpr ", ";
      fprint_valprim (pf | out, vp);
      strpr ")"
    end // end of [INSTRdefine_val]
  | INSTRextern cmd => begin
      fprintf1_exn (pf | out, "INSTRextern(\"%s\")", @(cmd))
    end // end of [INSTRextern]
  | INSTRextval (name, vp) => begin
      strpr "INSTRextval(";
      fprint1_string (pf | out, name);
      strpr ", ";
      fprint_valprim (pf | out, vp);
      strpr ")"
    end // end of [INSTRextval]
  | INSTRfreeptr vp => begin
      strpr "INSTRfreeptr("; fprint_valprim (pf | out, vp); strpr ")"
    end // end of [INSTRfreeptr]
  | INSTRfunction _ => begin
      fprint1_string (pf | out, "INSTRfunction(...)")
    end // end of [INSTRfunction]
  | INSTRfunlab fl => begin
      strpr "INSTRfunlab("; fprint_funlab (pf | out, fl); strpr ")"
    end // end of [INSTRfunlab]
  | INSTRdynload_file (fil) => begin
      strpr "INSTRdynload_file(";
      $Fil.fprint_filename (pf | out, fil);
      strpr ")"
    end // end of [INSTRdynload]
  | INSTRload_ptr (tmp, vp_ptr) => begin
      strpr "INSTRload_ptr(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_valprim (pf | out, vp_ptr);
      strpr ")"
    end // end of [INSTRload_ptr]
  | INSTRload_ptr_offs (tmp, vp_ptr, offs) => begin
      strpr "INSTRload_ptr_offs(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_valprim (pf | out, vp_ptr);
      strpr "; ";
      fprint_offsetlst (pf | out, offs);
      strpr ")"
    end // end of [INSTRload_ptr_offs]
  | INSTRload_var (tmp, vp_var) => begin
      strpr "INSTRload_var(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_valprim (pf | out, vp_var);
      strpr ")"
    end // end of [INSTRload_var]
  | INSTRload_var_offs (tmp, vp_var, offs) => begin
      strpr "INSTRload_var_offs(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_valprim (pf | out, vp_var);
      strpr "; ";
      fprint_offsetlst (pf | out, offs);
      strpr ")"
    end // end of [INSTRload_var_offs]
  | INSTRloop _ => begin
      fprint1_string (pf | out, "INSTRloop(...)")
    end // end of [INSTRloop]
  | INSTRloopexn (knd, tl) => begin
      strpr "INSTRloopexn(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_tmplab (pf | out, tl);
      strpr ")"
    end // end of [INSTRloopexn]
  | INSTRmove_arg (arg, vp) => begin
      strpr "INSTRmove_arg(";
      fprint1_int (pf | out, arg);
      strpr ", ";
      fprint_valprim (pf | out, vp);
      strpr ")"
    end // end of [INSTRmove_arg]
  | INSTRmove_con (tmp, hit_sum, d2c, vps_arg) => begin
      strpr "INSTRmove_con(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_hityp (pf | out, hityp_decode hit_sum);
      strpr "; ";
      fprint_d2con (pf | out, d2c);
      strpr "; ";
      fprint_valprimlst (pf | out, vps_arg);
      strpr ")"
    end // end of [INSTRmove_con]
  | INSTRmove_lazy_delay (tmp, lin, hit, vp) => begin
      strpr "INSTRmove_lazy_delay(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_int (pf | out, lin);
      strpr "; ";
      fprint_hityp (pf | out, hityp_decode hit);
      strpr "; ";
      fprint_valprim (pf | out, vp);
      strpr ")"
    end // end of [INSTRlazy_force]
  | INSTRmove_lazy_force (tmp, lin, hit, vp) => begin
      strpr "INSTRmove_lazy_force(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_int (pf | out, lin);
      strpr "; ";
      fprint_hityp (pf | out, hityp_decode hit);
      strpr "; ";
      fprint_valprim (pf | out, vp);
      strpr ")"
    end // end of [INSTRlazy_force]
  | INSTRmove_rec_box (tmp, hit_rec, lvps) => begin
      strpr "INSTRmove_rec_box(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_hityp (pf | out, hityp_decode hit_rec);
      strpr "; ";
      fprint_labvalprimlst (pf | out, lvps);
      strpr ")"
    end // end of [INSTRmove_rec_box]
  | INSTRmove_rec_flt (tmp, hit_rec, lvps) => begin
      strpr "INSTRmove_rec_flt(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_hityp (pf | out, hityp_decode hit_rec);
      strpr "; ";
      fprint_labvalprimlst (pf | out, lvps);
      strpr ")"
    end // end of [INSTRmove_rec_flt]
  | INSTRmove_val (tmp, vp) => begin
      strpr "INSTRmove_val(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_valprim (pf | out, vp);
      strpr ")"
    end // end of [INSTRmove_val]
  | INSTRmove_ref (tmp, vp) => begin
      strpr "INSTRmove_ref(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_valprim (pf | out, vp);
      strpr ")"
    end // end of [INSTRmove_ref]
  | INSTRpar_spawn (tmp_ret, vp_fun) => begin
      strpr "INSTRpar_spawn(";
      fprint_tmpvar (pf | out, tmp_ret);
      strpr "; ";
      fprint_valprim (pf | out, vp_fun);
      strpr ")"
    end // end of [INSTRpar_spawn]
  | INSTRpar_synch (tmp_ret) => begin
      strpr "INSTRpar_synch(";
      fprint_tmpvar (pf | out, tmp_ret);
      strpr ")"
    end // end of [INSTRpar_synch]
  | INSTRpatck (vp, patck, k_fail) => begin
      strpr "INSTRpatck(";
      fprint_valprim (pf | out, vp);
      strpr "; ";
      fprint_patck (pf | out, patck);
      strpr "; ";
      fprint_kont (pf | out, k_fail);
      strpr ")"
    end // end of [INSTRpatck]
  | INSTRraise vp => begin
      strpr "INSTRraise("; fprint_valprim (pf | out, vp); strpr ")"
    end // end of [INSTRraise]
  | INSTRselcon (tmp, vp_sum, hit_sum, i) => begin
      strpr "INSTRselcon(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_valprim (pf | out, vp_sum);
      strpr "; ";
      fprint_hityp (pf | out, hityp_decode hit_sum);
      strpr "; ";
      fprint1_int (pf | out, i);
      strpr ")"
    end // end of [INSTRselcon]
  | INSTRselcon_ptr (tmp, vp_sum, hit_sum, i) => begin
      strpr "INSTRselcon_ptr(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_valprim (pf | out, vp_sum);
      strpr "; ";
      fprint_hityp (pf | out, hityp_decode hit_sum);
      strpr "; ";
      fprint_int (pf | out, i);
      strpr ")"
    end // end of [INSTRselcon_ptr]
  | INSTRselect (tmp, vp_root, offs) => begin
      strpr "INSTRselect(";
      fprint_tmpvar (pf | out, tmp);
      strpr "; ";
      fprint_valprim (pf | out, vp_root);
      strpr "; ";
      fprint_offsetlst (pf | out, offs);
      strpr ")"
    end // end of [INSTRselect]
  | INSTRstore_ptr (vp_ptr, vp_val) => begin
      strpr "INSTRstore_ptr(";
      fprint_valprim (pf | out, vp_ptr);
      strpr "; ";
      fprint_valprim (pf | out, vp_val);
      strpr ")"
    end // end of [INSTRstore_ptr]
  | INSTRstore_ptr_offs (vp_ptr, offs, vp_val) => begin
      strpr "INSTRstore_ptr_offs(";
      fprint_valprim (pf | out, vp_ptr);
      strpr "; ";
      fprint_offsetlst (pf | out, offs);
      strpr "; ";
      fprint_valprim (pf | out, vp_val);
      strpr ")"
    end // end of [INSTRstore_ptr_offs]
  | INSTRstore_var (vp_var, vp_val) => begin
      strpr "INSTRstore_var(";
      fprint_valprim (pf | out, vp_var);
      strpr "; ";
      fprint_valprim (pf | out, vp_val);
      strpr ")"
    end // end of [INSTRstore_var]
  | INSTRstore_var_offs (vp_var, offs, vp_val) => begin
      strpr "INSTRstore_var_offs(";
      fprint_valprim (pf | out, vp_var);
      strpr "; ";
      fprint_offsetlst (pf | out, offs);
      strpr "; ";
      fprint_valprim (pf | out, vp_val);
      strpr ")"
    end // end of [INSTRstore_var_offs]
  | INSTRswitch _ => begin
      fprint1_string (pf | out, "INSTRswitch(...)")
    end // end of [INSTRswitch]
  | INSTRtmplabint (tl, i) => begin
      strpr "INSTRtmplabint(";
      fprint_tmplab (pf | out, tl);
      strpr "_";
      fprint1_int (pf | out, i);
      strpr ")"
    end // end of [INSTRtmplabint]
  | INSTRtrywith _ => begin
      fprint1_string (pf | out, "INSTRtrywith(...)")
    end // end of [INSTRtrywith]
  | INSTRvardec tmp => begin
      strpr "INSTRvardec("; fprint_tmpvar (pf | out, tmp); strpr ")"
    end // end of [INSTRvardec]
(*
  | _ => begin
      strpr "fprint_instr: not yet implemented.");
      fprint_newline (pf | out);
      $Err.abort {void} ()
    end // end of [_]
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
  fprint1_string (pf | out, ": "); fprint_newline (pf | out);
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
