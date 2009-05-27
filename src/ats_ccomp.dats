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

// Time: March 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

%{^

#include "ats_counter.cats" /* only needed for [ATS/Geizella] */

%}

(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"
staload Lst = "ats_list.sats"
staload Stamp = "ats_stamp.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_dynexp2.sats"
staload "ats_trans2_env.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"
staload "ats_ccomp.sats"
staload "ats_ccomp_env.sats"

(* ****** ****** *)

#define THISFILENAME "ats_ccomp.dats"

(* ****** ****** *)

typedef stamp_t = $Stamp.stamp_t

(* ****** ****** *)

local

typedef tmplab = '{ tmplab_stamp = stamp_t }
assume tmplab_t = tmplab

in // in of [local]

fn _tmplab_make (): tmplab = '{
  tmplab_stamp= $Stamp.tmplab_stamp_make ()
} // end of [tmplab]

implement tmplab_make () = _tmplab_make ()

implement tmplab_stamp_get (tl) = tl.tmplab_stamp

implement fprint_tmplab (pf | out, tl) = begin
  fprint1_string (pf | out, "__ats_lab_");
  $Stamp.fprint_stamp (pf | out, tl.tmplab_stamp)
end // end of [fprint_tmplab]

end // end of [local]

(* ****** ****** *)

local

typedef tmpvar = '{
  tmpvar_typ= hityp_t
, tmpvar_ret= int (* return status *)
, tmpvar_root= tmpvaropt
, tmpvar_stamp= stamp_t (* uniquicity *)
} // end of [tmpvar]

assume tmpvar_t = tmpvar

in // in of [local]

extern typedef "tmpvar_t" = tmpvar

implement fprint_tmpvar (pf | out, tmp) = begin
  fprint1_string (pf | out, "tmp(");
  $Stamp.fprint_stamp (pf | out, tmp.tmpvar_stamp);
  fprint1_string (pf | out, ")")
end // end of [fprint_tmpvar]

//

implement eq_tmpvar_tmpvar (tmp1, tmp2) =
  $Stamp.eq_stamp_stamp (tmp1.tmpvar_stamp, tmp2.tmpvar_stamp)
// end of [val]

implement compare_tmpvar_tmpvar (tmp1, tmp2) =
  $Stamp.compare_stamp_stamp (tmp1.tmpvar_stamp, tmp2.tmpvar_stamp)
// end of [val]

//

implement tmpvar_make (hit) = let
  val stamp = $Stamp.tmpvar_stamp_make () in '{
  tmpvar_typ= hit
, tmpvar_ret= 0
, tmpvar_root= TMPVAROPTnone ()
, tmpvar_stamp= stamp
} end // end of [tmpvar_make]

extern fun tmpvar_ret_set (tmp: tmpvar, ret: int): void
  = "ats_ccomp_tmpvar_ret_set"

implement tmpvar_make_ret (hit) = let
  val tmp = tmpvar_make (hit)
  val () = tmpvar_ret_set (tmp, 1)
in
  tmp
end // end of [tmpvar_make_ret]

extern fun tmpvar_root_set (tmp: tmpvar, otmp: tmpvaropt): void
  = "ats_ccomp_tmpvar_root_set"

implement tmpvar_make_root (tmp) = let
  val otmp = (
    case+ tmp.tmpvar_root of
    | TMPVAROPTnone () => TMPVAROPTsome tmp | otmp => otmp
  ) : tmpvaropt
  val () = tmpvar_root_set (tmp, otmp)
in
  tmp
end // end of [tmpvar_make_root]

//

implement tmpvarlst_make (hits) = let
  val hits = hityplst_decode (hits)
  fn aux (hit: hityp): tmpvar_t = tmpvar_make (hityp_encode hit)
in
  $Lst.list_map_fun (hits, aux) 
end // end of [tmpvarlst_make]

//

implement tmpvar_ret_get (tmp) = tmp.tmpvar_ret
implement tmpvar_root_get (tmp) = tmp.tmpvar_root
implement tmpvar_stamp_get (tmp) = tmp.tmpvar_stamp
implement tmpvar_typ_get (tmp) = tmp.tmpvar_typ

implement tmpvar_is_void (tmp) = hityp_t_is_void (tmp.tmpvar_typ)

implement tmpvar_is_nonvoid (tmp) = begin
  if hityp_t_is_void (tmp.tmpvar_typ) then false else true
end // end of [tmpvar_is_nonvoid]

end // end of [local]

(* ****** ****** *)

local

typedef funlab = '{
  funlab_name= string
, funlab_lev= int
, funlab_typ= hityp_t (* function type *)
, funlab_qua= d2cstopt (* local or global *)
, funlab_stamp= stamp_t
, funlab_tailjoined= tmpvarlst (* tail-call optimization *)
, funlab_entry= funentryopt
, funlab_trmck= int (* trmck function status *)
} // end of [typedef]

assume funlab_t = funlab

in // in of [local]

extern typedef "funlab_t" = funlab

implement fprint_funlab (pf | out, fl) = begin
  fprint1_string (pf | out, fl.funlab_name)
end // end of [fprint_funlab]

implement eq_funlab_funlab (fl1, fl2) = begin
  $Stamp.eq_stamp_stamp (fl1.funlab_stamp, fl2.funlab_stamp)
end // end of [eq_funlab_funlab]

implement compare_funlab_funlab (fl1, fl2) = begin
  $Stamp.compare_stamp_stamp (fl1.funlab_stamp, fl2.funlab_stamp)
end // end of [compare_funlab_funlab]

(* ****** ****** *)

fn _funlab_make (
    name: string, level: int, hit: hityp_t, stamp: stamp_t, trmck: int
  ) : funlab = '{
  funlab_name= name
, funlab_lev= level
, funlab_typ= hit
, funlab_qua= D2CSTOPTnone ()
, funlab_stamp= stamp
, funlab_tailjoined= list_nil ()
, funlab_entry= None ()
, funlab_trmck= trmck
} // end of [funlab_make]

implement funlab_make_typ (hit) = let
  val level = d2var_current_level_get ()
  val stamp = $Stamp.funlab_stamp_make ()
  val name = "__ats_fun_" + $Stamp.tostring_stamp stamp
in
  _funlab_make (name, level, hit, stamp, 0(*trmck*))
end // end of [funlab_make_typ]

implement funlab_make_nam_typ (name, hit) = let
  val level = d2var_current_level_get ()
  val stamp = $Stamp.funlab_stamp_make ()
in
  _funlab_make (name, level, hit, stamp, 0(*trmck*))
end // end of [funlab_make_nam_typ]

(* ****** ****** *)

fn global_cst_name_make (d2c: d2cst_t): string = let
  val ext = d2cst_ext_get d2c
in
  if stropt_is_none (ext) then let
    val d2c_name = $Sym.symbol_name (d2cst_sym_get d2c)
  in
    case+ d2cst_kind_get d2c of
    | $Syn.DCSTKINDval () => d2c_name + "$fun" | _ => d2c_name
  end else begin
    stropt_unsome (ext)
  end // end of [if]
end // end of [global_cst_name_make]

implement funlab_make_cst_typ (d2c, tmparg, hit) = let
  val is_global =
    (case+ tmparg of list_cons _ => false | _ => true): bool
  val name: string = (
    if is_global then begin
      global_cst_name_make (d2c)
    end else let
      val tmparg = hityplstlst_normalize (tmparg)
    in
      template_cst_name_make (d2c, tmparg)
    end // end of [if]
  ) : string
(*
  val () = begin
    prerr "funlab_make_cst_type: name = "; prerr name; prerr_newline ()
  end // end of [val]
*)
  val level = d2var_current_level_get ()
  val stamp = $Stamp.funlab_stamp_make ()
  val fl = _funlab_make (name, level, hit, stamp, 0(*trmck*))
  // note that template instantiation is always *local* !!!
  val () = if is_global then funlab_qua_set (fl, D2CSTOPTsome d2c)
in
  fl
end // end of [funlab_make_cst_typ]

implement funlab_make_var_typ (d2v, hit) = let
  val d2v_name = $Sym.symbol_name (d2var_sym_get d2v)
  val level = d2var_current_level_get ()
  val stamp = $Stamp.funlab_stamp_make ()
  val stamp_name = $Stamp.tostring_stamp stamp
  val name = tostringf ("%s_%s", @(d2v_name, stamp_name))
in
  _funlab_make (name, level, hit, stamp, 0(*trmck*))
end // end of [funlab_make_var_typ]

(* ****** ****** *)

implement funlab_make_cst_trmck (d2c) = let
  val name = global_cst_name_make (d2c)
  val hit = hityp_encode (
    hityp_fun ($Syn.FUNCLOfun (), list_nil (), hityp_void)
  ) // end of [val]
  val stamp = $Stamp.funlab_stamp_make ()
  val fl = _funlab_make (name, 0(*level*), hit, stamp, 1(*trmck*))
  val () = funlab_qua_set (fl, D2CSTOPTsome d2c)
in
  fl
end // end of [funlab_make_cst_trmck] 

(* ****** ****** *)

implement funlab_name_get (fl) = fl.funlab_name

implement funlab_lev_get (fl) = fl.funlab_lev

implement funlab_typ_get (fl) = fl.funlab_typ

implement funlab_typ_arg_get (fl) = let
  val hit_fun = hityp_decode (fl.funlab_typ) in
  case+ hit_fun.hityp_node of
  | HITfun (_(*fc*), hits_arg, _(*hit_res*)) =>
      hityplst_encode (hits_arg)
  | _ => begin
      prerr "INTERNAL ERROR";
      prerr ": funlab_typ_arg_get: hit_fun = "; prerr_hityp hit_fun;
      prerr_newline ();
      $Err.abort {hityplst_t} ()
    end
end // end of [funlab_typ_arg_get]

implement funlab_typ_res_get (fl) = let
  val hit_fun = hityp_decode (fl.funlab_typ) in
  case+ hit_fun.hityp_node of
  | HITfun (_(*fc*), _(*hits_arg*), hit_res) =>
      hityp_encode (hit_res)
  | _ => begin
      prerr "INTERNAL ERROR";
      prerr ": funlab_typ_res_get: hit_fun = "; prerr_hityp hit_fun;
      prerr_newline ();
      $Err.abort {hityp_t} ()
    end // end of [_]
end // end of [funlab_typ_res_get]

implement funlab_funclo_get (fl) = let
  val hit_fun = hityp_decode (fl.funlab_typ) in
  case+ hit_fun.hityp_node of
  | HITfun (funclo, _(*hits_arg*), _(*hit_res*)) => funclo
  | _ => begin
      prerr "INTERNAL ERROR";
      prerr ": funlab_funclo_get: hit_fun = "; prerr_hityp hit_fun;
      prerr_newline ();
      $Err.abort {$Syn.funclo} ()
    end // end of [_]
end // end of [funlab_funclo_get]

implement funlab_qua_get (fl) = fl.funlab_qua

implement funlab_tailjoined_get (fl) = fl.funlab_tailjoined

implement funlab_entry_get (fl) = fl.funlab_entry

implement funlab_entry_get_some (fl) = begin
  case+ fl.funlab_entry of
  | Some entry => entry | None () => begin
      prerr "Internal Error";
      $Deb.debug_prerrf (": %s", @(THISFILENAME));
      prerr ": funlab_entry_get_some";
      prerr ": no entry assocated with ["; prerr_funlab fl; prerr "]";
      prerr_newline ();
      $Err.abort {funentry_t} ()
    end // end of [None]
end (* end of [funlab_entry_get_some] *)

implement funlab_trmck_get (fl) = fl.funlab_trmck

end // end of [local]

(* ****** ****** *)

implement valprim_is_const (vp) = begin
  case+ vp.valprim_node of
  | VPbool _ => true
  | VPchar _ => true
  | VPcst _ => true
  | VPfloat _ => true
  | VPfun _ => true
  | VPint _ => true
  | VPsizeof _ => true
  | VPstring _ => true
  | VPtop _ => true
  | VPvoid _ =>true
  | _ => false
end (* end of [valprim_is_const] *)

(* ****** ****** *)

implement valprim_is_mutable (vp) = begin
  case+ vp.valprim_node of
  | VParg_ref _ => true | VPtmp_ref _ => true | _ => false
end // end of [valprim_is_mutable]

(* ****** ****** *)

implement valprim_arg (n, hit) = '{
  valprim_node= VParg (n), valprim_typ= hit
}

implement valprim_arg_ref (n, hit) = '{
  valprim_node= VParg_ref (n), valprim_typ= hit
}

implement valprim_bool (b) = '{
  valprim_node= VPbool b, valprim_typ= hityp_encode (hityp_bool)
}

implement valprim_char (c) = '{
  valprim_node= VPchar c, valprim_typ= hityp_encode (hityp_char)
}

implement valprim_cst (d2c, hit) = '{
  valprim_node= VPcst (d2c), valprim_typ= hit
}

implement valprim_env (vt, hit) = '{
  valprim_node= VPenv vt, valprim_typ= hit
}

implement valprim_ext (code, hit) = '{
  valprim_node= VPext code, valprim_typ= hit
}

implement valprim_float f(*string*) = '{
  valprim_node= VPfloat f, valprim_typ= hityp_encode (hityp_double)
}

implement valprim_clo (knd, fl, env) = let
  val hit = (if knd <> 0 then hityp_ptr else hityp_clo): hityp
in '{
  valprim_node= VPclo (knd, fl, env), valprim_typ= hityp_encode hit
} end // end of [valprim_clo]

implement valprim_fun (funlab) = '{
  valprim_node= VPfun funlab, valprim_typ= funlab_typ_get funlab
} // end of [valprim_fun]

(* ****** ****** *)

implement valprim_int (int) = '{
  valprim_node= VPint (int)
, valprim_typ= hityp_encode (hityp_int)
}

implement valprim_intsp (str, int) = '{
  valprim_node= VPintsp (str, int)
, valprim_typ= hityp_encode (hityp_int)
}

(* ****** ****** *)

implement valprim_ptrof (vp) = '{
  valprim_node= VPptrof vp
, valprim_typ= hityp_encode (hityp_ptr)
}

implement valprim_ptrof_ptr_offs
  (vp, offs) = begin case+ offs of
  | list_cons _ => '{
      valprim_node= VPptrof_ptr_offs (vp, offs)
    , valprim_typ= hityp_encode (hityp_ptr)
    }
  | list_nil () => valprim_ptrof (vp)
end // end of [valprim_ptrof_ptr_offs]

implement valprim_ptrof_var_offs
  (vp, offs) = begin case+ offs of
  | list_cons _ => '{
      valprim_node= VPptrof_var_offs (vp, offs)
    , valprim_typ= hityp_encode (hityp_ptr)
    }
  | list_nil () => valprim_ptrof (vp)
end // end of [valprim_ptrof_var_offs]

(* ****** ****** *)

implement valprim_sizeof (hit) = '{
  valprim_node= VPsizeof hit
, valprim_typ= hityp_encode (hityp_int)
}

implement valprim_string (str, len) = '{
  valprim_node= VPstring (str, len)
, valprim_typ= hityp_encode (hityp_string)
}

implement valprim_tmp (tmp) = '{
  valprim_node= VPtmp tmp, valprim_typ= tmpvar_typ_get tmp
}

implement valprim_tmp_ref (tmp) = '{
  valprim_node= VPtmp_ref tmp, valprim_typ= tmpvar_typ_get tmp
}

implement valprim_top (hit) = '{
  valprim_node= VPtop (), valprim_typ= hit
}

implement valprim_void () = '{
  valprim_node= VPvoid (), valprim_typ= hityp_encode (hityp_void)
}

(* ****** ****** *)

implement valprim_is_void (vp) = begin
  hityp_is_void (hityp_decode vp.valprim_typ)
end // end of [valprim_is_void]

(* ****** ****** *)

implement instr_add_arr_heap (res, tmp_res, asz, hit_elt) = begin
  res := list_vt_cons (INSTRarr_heap (tmp_res, asz, hit_elt), res)
end // end of [instr_add_arr_heap]

implement instr_add_arr_stack (res, tmp_res, vp_asz, hit_elt) = begin
  res := list_vt_cons (INSTRarr_stack (tmp_res, vp_asz, hit_elt), res)
end // end of [instr_add_arr_stack]

//

implement instr_add_assgn_arr
  (res, vp_arr, vp_asz, tmp_elt, vp_tsz) = res :=
  list_vt_cons (INSTRassgn_arr (vp_arr, vp_asz, tmp_elt, vp_tsz), res)
// end of [instr_add_assgn_arr]

implement instr_add_assgn_clo (res, vp_clo, fl, env) =
  res := list_vt_cons (INSTRassgn_clo (vp_clo, fl, env), res)
// end of [instr_add_assgn_clo]

//

implement instr_add_call
  (res, tmp_res, hit_fun, vp_fun, vps_arg) = begin
  res := list_vt_cons (INSTRcall (tmp_res, hit_fun, vp_fun, vps_arg), res)
end // end of [instr_add_call]

implement instr_add_call_tail (res, fl) =
  res := list_vt_cons (INSTRcall_tail fl, res)

//

implement instr_add_define_clo (res, d2c, fl) =
  res := list_vt_cons (INSTRdefine_clo (d2c, fl), res)

implement instr_add_define_fun (res, d2c, fl) =
  res := list_vt_cons (INSTRdefine_fun (d2c, fl), res)

implement instr_add_define_val (res, d2c, vp) =
  res := list_vt_cons (INSTRdefine_val (d2c, vp), res)

//

implement instr_add_extval (res, name, vp) =
  res := list_vt_cons (INSTRextval (name, vp), res)

implement instr_add_freeptr (res, vp) =
  res := list_vt_cons (INSTRfreeptr (vp), res)

implement instr_add_patck (res, vp, patck, fail) =
  res := list_vt_cons (INSTRpatck (vp, patck, fail), res)

//

implement instr_add_dynload_file (res, fil) =
  res := list_vt_cons (INSTRdynload_file fil, res)

//

implement instr_add_load_ptr_offs (res, tmp, vp, offs) = let
  val ins = case+ offs of
    | list_cons _ => INSTRload_ptr_offs (tmp, vp, offs)
    | list_nil () => INSTRload_ptr (tmp, vp)
in
  res := list_vt_cons (ins, res)
end // end of [instr_add_load_ptr_offs]

implement instr_add_load_var_offs (res, tmp, vp, offs) = let
  val ins = case+ offs of
    | list_cons _ => INSTRload_var_offs (tmp, vp, offs)
    | list_nil () => INSTRload_var (tmp, vp)
in
  res := list_vt_cons (ins, res)
end // end of [instr_add_load_var_offs]

//

implement instr_add_loop (
    res
  , lab_init, lab_fini, lab_cont
  , inss_init
  , vp_test, inss_test
  , inss_post
  , inss_body
  ) = let
  val ins = INSTRloop (
    lab_init, lab_fini, lab_cont, inss_init, vp_test, inss_test, inss_post, inss_body
  ) // end of [INSTRloop]
in
  res := list_vt_cons (ins, res)
end // end of [instr_add_loop]

implement instr_add_loopexn (res, knd, tl) = 
  res := list_vt_cons (INSTRloopexn (knd, tl), res)

//

implement instr_add_move_arg (res, arg, vp) =
  res := list_vt_cons (INSTRmove_arg (arg, vp), res)

implement instr_add_move_con (res, tmp_res, hit_sum, d2c, vps_arg) =
  res := list_vt_cons (INSTRmove_con (tmp_res, hit_sum, d2c, vps_arg), res)

//

implement instr_add_move_lazy_delay (res, tmp_res, lin, hit_body, vp_clo) =
  res := list_vt_cons (INSTRmove_lazy_delay (tmp_res, lin, hit_body, vp_clo), res)

implement instr_add_move_lazy_force (res, tmp_res, lin, hit_val, vp_lazy) =
  res := list_vt_cons (INSTRmove_lazy_force (tmp_res, lin, hit_val, vp_lazy), res)

//

implement instr_add_move_rec
  (res, tmp_res, recknd, hit_rec, lvps) = let
  val ins = (case+ 0 of
    | _ when recknd = 0 => INSTRmove_rec_flt (tmp_res, hit_rec, lvps)
    | _ when recknd > 0 => INSTRmove_rec_box (tmp_res, hit_rec, lvps)
    | _ => begin
        prerr "Internal Error: instr_add_move_rec: recknd = ";
        prerr recknd; prerr_newline ();
        $Err.abort {instr} ()
      end // end of [_]
    ) : instr
in
  res := list_vt_cons (ins, res)
end // end of [instr_add_move_rec]

implement instr_add_move_ref (res, tmp_res, vp) =
  res := list_vt_cons (INSTRmove_ref (tmp_res, vp), res)

implement instr_add_move_val (res, tmp_res, vp) =
  res := list_vt_cons (INSTRmove_val (tmp_res, vp), res)

//

implement instr_add_raise (res, vp_exn) =
  res := list_vt_cons (INSTRraise vp_exn, res)

//

implement instr_add_select (res, tmp_res, vp_root, offs) =
  res := list_vt_cons (INSTRselect (tmp_res, vp_root, offs), res)

implement instr_add_selcon (res, tmp_res, vp_sum, hit_sum, i) =
  res := list_vt_cons (INSTRselcon (tmp_res, vp_sum, hit_sum, i), res)

implement instr_add_selcon_ptr (res, tmp_res, vp_sum, hit_sum, i) =
  res := list_vt_cons (INSTRselcon_ptr (tmp_res, vp_sum, hit_sum, i), res)

//

implement instr_add_store_ptr_offs
  (res, vp_ptr, offs, vp_val) = let
  val ins = case+ offs of
    | list_cons _ => INSTRstore_ptr_offs (vp_ptr, offs, vp_val)
    | list_nil () => INSTRstore_ptr (vp_ptr, vp_val)
in
  res := list_vt_cons (ins, res)
end // end of [instr_add_store_ptr_offs]

implement instr_add_store_var_offs
  (res, vp_mut, offs, vp_val) = let
  val ins = case+ offs of
    | list_cons _ => INSTRstore_var_offs (vp_mut, offs, vp_val)
    | list_nil () => INSTRstore_var (vp_mut, vp_val)
in
  res := list_vt_cons (ins, res)
end // end of [instr_add_store_var_offs]

//

implement instr_add_switch (res, brs) =
  res := list_vt_cons (INSTRswitch brs, res)

implement instr_add_tmplabint (res, tl, i) =
  res := list_vt_cons (INSTRtmplabint (tl, i), res)

implement instr_add_trywith (res, res_try, tmp_exn, brs) =
  res := list_vt_cons (INSTRtrywith (res_try, tmp_exn, brs), res)

implement instr_add_vardec (res, tmp) =
  res := list_vt_cons (INSTRvardec tmp, res)

(* ****** ****** *)

%{$

ats_void_type
ats_ccomp_funlab_qua_set
  (ats_ptr_type fl, ats_ptr_type od2c) {
  ((funlab_t)fl)->atslab_funlab_qua = od2c ; return ;
}

ats_void_type
ats_ccomp_funlab_entry_set
  (ats_ptr_type fl, ats_ptr_type entry) {
  ((funlab_t)fl)->atslab_funlab_entry = entry ; return ;
}

ats_void_type
ats_ccomp_funlab_tailjoined_set
  (ats_ptr_type fl, ats_ptr_type tmps) {
  ((funlab_t)fl)->atslab_funlab_tailjoined = tmps ; return ;
}

ats_void_type
ats_ccomp_tmpvar_ret_set
  (ats_ptr_type tmp, ats_int_type ret) {
  ((tmpvar_t)tmp)->atslab_tmpvar_ret = ret ; return ;
}

ats_void_type
ats_ccomp_tmpvar_root_set
  (ats_ptr_type tmp, ats_ptr_type root) {
  ((tmpvar_t)tmp)->atslab_tmpvar_root = root ; return ;
}

%}

(* ****** ****** *)

(* end of [ats_ccomp.dats] *)
