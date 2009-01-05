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

// Time: December 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

(* Mainly for handling dynamic expressions during type-checking *)

(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Eff = "ats_effect.sats"
staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"
staload Mac = "ats_macro2.sats"
staload SOL = "ats_staexp2_solve.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_stadyncst2.sats"
staload "ats_patcst2.sats"
staload "ats_dynexp3.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_trans3.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

#define THISFILENAME "ats_trans3_exp_up.dats"

(* ****** ****** *)

extern val "FLOATKINDfloat" = $Syn.FLOATKINDfloat ()
extern val "FLOATKINDdouble" = $Syn.FLOATKINDdouble ()
extern val "FLOATKINDdouble_long" = $Syn.FLOATKINDdouble_long ()
extern val "FLOATKINDnone" = $Syn.FLOATKINDnone ()

extern val "INTKINDint" = $Syn.INTKINDint ()
extern val "INTKINDlint" = $Syn.INTKINDlint ()
extern val "INTKINDuint" = $Syn.INTKINDuint ()
extern val "INTKINDulint" = $Syn.INTKINDulint ()
extern val "INTKINDnone" = $Syn.INTKINDnone ()

%{$

ats_ptr_type ats_trans3_floatkind_eval (ats_ptr_type s0) {
  char *s ;

  s = s0 ; while (*s) { ++s ; } ; --s ;
  switch (*s) {
    case 'f': case 'F': return FLOATKINDfloat ;
    case 'd': case 'D': return FLOATKINDdouble ;
    case 'l': case 'L': return FLOATKINDdouble_long ;
    default : ;
  }
  return FLOATKINDnone ;
}

ats_ptr_type ats_trans3_intkind_eval (ats_ptr_type s0) {
  char c, *s ; int nL, nU ;
  s = s0 ; nL = 0 ; nU = 0 ;
  while (c = *s) {
    s += 1 ;
    switch (c) {
      case 'l': case 'L': ++nL ; break ;
      case 'u': case 'U': ++nU ; break ;
      default : break ;
    }
  }

  if (nL == 0 && nU == 0) return INTKINDint ; /* deadcode */
  if (nL == 1 && nU == 0) return INTKINDlint ; /* long */
  if (nL == 0 && nU == 1) return INTKINDuint ; /* unsigned */
  if (nL == 1 && nU == 1) return INTKINDulint ; /* unsigned */
  return INTKINDnone ;
}

%}

(* ****** ****** *)

overload prerr with $Loc.prerr_location

(* ****** ****** *)

typedef funclo =  $Syn.funclo

fn d2exp_funclo_of_d2exp
  (d2e0: d2exp, fc0: &funclo): d2exp = begin
  case+ :(fc0: funclo) => d2e0.d2exp_node of
  | D2Eann_funclo (d2e, fc) => (fc0 := fc; d2e) | _ => d2e0
end // end of [d2exp_funclo_of_d2exp]

//

fn s2eff_of_d2exp (d2e0: d2exp): s2eff =
  case+ d2e0.d2exp_node of
  | D2Eann_seff (_, s2fe) => s2fe
  | D2Elam_dyn _ => S2EFFnil ()
  | D2Elam_sta _ => S2EFFnil ()
  | _ => S2EFFall ()

fn d2exp_s2eff_of_d2exp
  (d2e0: d2exp, s2fe0: &(s2eff?) >> s2eff): d2exp =
  case+ :(s2fe0: s2eff) => d2e0.d2exp_node of
  | D2Eann_seff (d2e, s2fe) => (s2fe0 := s2fe; d2e)
  | D2Elam_dyn _ => (s2fe0 := S2EFFnil (); d2e0)
  | D2Elam_sta _ => (s2fe0 := S2EFFnil (); d2e0)
  | _ => (s2fe0 := S2EFFall (); d2e0)

(* ****** ****** *)

fn d2exp_seq_typ_syn (d2es: d2explst): s2exp = let
  fun aux (d2e: d2exp, d2es: d2explst): s2exp = case+ d2es of
    | cons (d2e, d2es) => aux (d2e, d2es) | nil () => d2exp_typ_syn d2e
in
  case+ d2es of
    cons (d2e, d2es) => aux (d2e, d2es) | nil () => s2exp_void_t0ype ()
end // end of [d2exp_seq_typ_syn]

implement d2exp_typ_syn (d2e0) = begin
  case+ d2e0.d2exp_node of
  | D2Eann_type (_, s2e) => s2e
  | D2Eann_seff (d2e, _) => d2exp_typ_syn (d2e)
  | D2Eann_funclo (d2e, _) => d2exp_typ_syn (d2e)
  | D2Eassgn _ => s2exp_void_t0ype ()
  | D2Echar _ => s2exp_char_t0ype ()
  | D2Ecst d2c => d2cst_typ_get d2c
  | D2Eeffmask (_, d2e) => d2exp_typ_syn (d2e)
  | D2Eempty () => s2exp_void_t0ype ()
  | D2Efix (_, d2e) => d2exp_typ_syn (d2e)
  | D2Efloat _ => s2exp_double_t0ype ()
  | D2Efor _ => s2exp_void_t0ype ()
  | D2Eint _ => s2exp_int_t0ype ()
  | D2Elam_dyn (lin, npf, p2ts_arg, d2e_body) => let
(*
      val () = begin
        prerr "d2exp_typ_syn: D2Elam_dyn: d2e_body = ";
        prerr d2e_body;
        prerr_newline ()
      end
*)
      val loc0 = d2e0.d2exp_loc
      val s2es_arg = p2atlst_typ_syn p2ts_arg
      val s2e_res = d2exp_typ_syn (d2e_body)
      var fc: funclo = $Syn.FUNCLOfun () // default
      val d2e_body = d2exp_funclo_of_d2exp (d2e_body, fc)
      val s2fe = s2eff_of_d2exp d2e_body
      val isprf = s2exp_is_proof s2e_res
      val s2t_fun: s2rt = s2rt_prf_lin_fc (loc0, isprf, lin > 0, fc)
      val s2e_fun = s2exp_fun_srt 
        (s2t_fun, fc, lin, s2fe, npf, s2es_arg, s2e_res)
(*
      val () = begin
        prerr "d2exp_typ_syn: D2Elam_dyn: s2e_fun = ";
        prerr s2e_fun;
        prerr_newline ()
      end
*)
    in
      s2e_fun
    end
  | D2Elam_met (r_d2vs, s2es_met, d2e) => begin
    case+ !r_d2vs of
    | cons _ => begin
        s2exp_metfn (None (), s2es_met, d2exp_typ_syn d2e)
      end
    | nil () => begin
        prerr d2e0.d2exp_loc;
        prerr ": error(3)";
        prerr ": illegal use of termination metric.";
        prerr_newline ();
        $Err.abort {s2exp} ()
      end
    end
  | D2Elam_sta (s2vs, s2ps, d2e) => begin
      s2exp_uni (s2vs, s2ps, d2exp_typ_syn d2e)
    end
  | D2Elet (_, d2e) => d2exp_typ_syn (d2e)
  | D2Estring (_(*str*), _(*len*)) => s2exp_string_type ()
  | D2Ewhere (d2e, _) => d2exp_typ_syn (d2e)
  | D2Ewhile _ => s2exp_void_t0ype ()
  | _ => let
      val s2e = s2exp_Var_make_srt (d2e0.d2exp_loc, s2rt_t0ype)
      val () = d2exp_typ_set (d2e0, Some s2e)
    in
      s2e
    end
end // end of [d2exp_typ_syn]

(* ****** ****** *)

implement d3exp_open_and_add (d3e) = let
  val s2e = s2exp_opnexi_and_add (d3e.d3exp_loc, d3e.d3exp_typ)
in
  d3exp_typ_set (d3e, s2e)
end

implement d3explst_open_and_add (d3es) = begin
  case+ d3es of
  | cons (d3e, d3es) => begin
      d3exp_open_and_add d3e; d3explst_open_and_add d3es 
    end
  | nil () => ()
end // end of [d3explst_open_and_add]

(* ****** ****** *)

fn pfarity_check_fun (loc_fun: loc_t, npf_fun: int, npf: int) =
  if npf_fun = npf then () else begin
    prerr loc_fun;
    prerr ": error(3)";
    prerr ": the proof arity of the function is [";
    prerr npf_fun;
    prerr "] but it is expected to be [";
    prerr npf;
    prerr "].";
    prerr_newline ();
    $Err.abort {void} ()
end

(* ****** ****** *)

fn d2lab_tr_up (d2l: d2lab): d3lab0 = case+ d2l.d2lab_node of
  | D2LABind d2ess => d3lab0_ind (d2l.d2lab_loc, d2explstlst_tr_up d2ess)
  | D2LABlab l => d3lab0_lab (d2l.d2lab_loc, l)

fun d2lablst_tr_up (d2ls: d2lablst): d3lab0lst = case+ d2ls of
  | cons (d2l, d2ls) => cons (d2lab_tr_up d2l, d2lablst_tr_up d2ls)
  | nil () => nil ()

//

fun s2lab0lst_of_d3lab0lst {n:nat} .<n>.
  (d3ls: list (d3lab0, n)): list (s2lab, n) = begin
  case+ d3ls of
  | cons (d3l, d3ls) => let
      val s2l = case+ d3l.d3lab0_node of
        | D3LAB0ind (d3ess) => S2LAB0ind (d3explstlst_ind_get d3ess)
        | D3LAB0lab l => S2LAB0lab l
    in
      cons (s2l, s2lab0lst_of_d3lab0lst d3ls)
    end
  | nil () => nil ()
end // end of [s2lab0lst_of_d3lab0lst]

(*

fun s2lab1lst_of_d3lab1lst {n:nat} .<n>.
  (d3ls: list (d3lab1, n)): list (s2lab, n) = begin
  case+ d3ls of
  | cons (d3l, d3ls) => let
      val s2l = case+ d3l.d3lab1_node of
        | D3LAB1ind (d3ess, s2e) => S2LAB1ind (d3explstlst_ind_get d3ess, s2e)
        | D3LAB1lab (l, s2e) => S2LAB1lab (l, s2e)
    in
      cons (s2l, s2lab1lst_of_d3lab1lst d3ls)
    end
  | nil () => nil ()
end // end of [s2lab2lst_of_d3lab1lst]

*)

fun d3lab1lst_of_d3lab0lst_s2lablst
  (d3ls: d3lab0lst, s2ls: s2lablst): d3lab1lst = begin
  case+ (d3ls, s2ls) of
  | (cons (d3l, d3ls), cons (s2l, s2ls)) => let
      val d3l_new = case+ d3l.d3lab0_node of
        | D3LAB0ind d3ess => begin case+ s2l of
          | S2LAB1ind (_, s2e_elt) => begin
              d3lab1_ind (d3l.d3lab0_loc, d3ess, s2e_elt)
            end
          | _ => begin
              prerr "Internal Error: d3lab1lst_of_d3lab0lst_s2lablst: D3LAB0ind";
              prerr_newline ();
              $Err.abort {d3lab1} ()
            end
          end
        | D3LAB0lab l => begin case+ s2l of
          | S2LAB1lab (l, s2e) => d3lab1_lab (d3l.d3lab0_loc, l, s2e)
          | _ => begin
              prerr "Internal Error";
              prerr ": d3lab1lst_of_d3lab0lst_s2lablst: D3LAB0lab: s2l = ";
              prerr s2l; prerr_newline ();
              $Err.abort {d3lab1} ()
            end
          end
    in
      cons (d3l_new, d3lab1lst_of_d3lab0lst_s2lablst (d3ls, s2ls))
    end
  | (nil (), nil ()) => nil ()
  | (_, _) => begin
      prerr "Internal Error: d3lab1lst_of_d3lab0lst_s2lablst: length mismatch";
      prerr_newline ();
      $Err.abort ()
    end
end // end of [d3lab1lst_of_d3lab0lst_s2lablst]

(* ****** ****** *)

fn d3exp_clo_restore (d3e: d3exp): d3exp = let
  val loc = d3e.d3exp_loc
  val s2e_fun = d3e.d3exp_typ
  val s2e_fun_new: s2exp = case+ s2e_fun.s2exp_node of
    | S2Efun (fc, lin, s2fe, npf, s2es_arg, s2e_res) => begin
      case+ lin of
      | _ when lin = 1 => s2exp_fun_srt
          (s2rt_type, fc, ~1(*topized*), s2fe, npf, s2es_arg, s2e_res)
      | _ when lin = 0 => s2e_fun
      | _ (* lin = ~1 *) => begin
          prerr loc;
          prerr ": error(3)";
          prerr ": a linear function cannot be applied repeatedly.";
          prerr_newline ();
          $Err.abort {s2exp} ()
        end
      end // end of [S2Efun]
    | _ => begin
        prerr loc;
        prerr ": Internal Error";
        prerr ": d3exp_clo_restore: not a function type: s2e_fun = ";
        prerr s2e_fun;
        prerr_newline ();
        $Err.abort {s2exp} ()
      end
  val freeknd = d3exp_lval_typ_set_arg (0(*val*), d3e, s2e_fun_new)
in
  d3exp_refarg (loc, s2e_fun_new, 0(*val*), freeknd, d3e)
end // end of [d3exp_clo_restore]

//

#define CLO 0; #define CLOPTR 1; #define CLOREF ~1

//

fn d3exp_funclo_restore
  (fc: $Syn.funclo, d3e_fun: d3exp): d3exp = begin
  case+ fc of
  | $Syn.FUNCLOclo knd => begin // knd: 1/0/~1: ptr/clo/ref
      if knd >= CLO then d3exp_clo_restore d3e_fun else d3e_fun
    end
  | $Syn.FUNCLOfun () => d3e_fun
end // end of [d3exp_funclo_restore]

//

fun d3explst_arg_restore
  (d3es: d3explst, wths2es: wths2explst): d3explst = begin
  case+ wths2es of
  | WTHS2EXPLSTcons_some (refval, s2e_res, wths2es) => let
      val () = assert_errmsg_bool1 (
        $Lst.list_is_cons d3es, "Interal Error: ats_trans3_exp: d3explst_arg_restore"
      ) // end of assert_errmsg
      val+ cons (d3e, d3es) = d3es
      val loc = d3e.d3exp_loc
      val s2e_res = s2exp_opnexi_and_add (loc, s2e_res)
(*
      val () = begin
        prerr "d3explst_arg_restore: d3e = "; prerr d3e; prerr_newline ();
        prerr "d3explst_arg_restore: d3e.typ = "; prerr d3e.d3exp_typ; prerr_newline ();
        prerr "d3explst_arg_restore: s2e_res = "; prerr s2e_res; prerr_newline ();
      end
*)
      val freeknd = d3exp_lval_typ_set_arg (refval, d3e, s2e_res)
      val d3e = d3exp_refarg (loc, s2e_res, refval, freeknd, d3e)
    in
      cons (d3e, d3explst_arg_restore (d3es, wths2es))
    end
  | WTHS2EXPLSTcons_none wths2es => let
      val () = assert_errmsg_bool1 (
        $Lst.list_is_cons d3es, "Interal Error: ats_trans3_exp: d3explst_arg_restore"
      ) // end of assert_errmsg
      val+ cons (d3e, d3es) = d3es
    in
      cons (d3e, d3explst_arg_restore (d3es, wths2es))
    end
  | WTHS2EXPLSTnil () => nil ()
end // end of [d3explst_arg_restore]

(* ****** ****** *)

datatype d23exp = D23Ed2exp of d2exp | D23Ed3exp of d3exp
typedef d23explst = List d23exp

fun d23explst_tr_up (d23es: d23explst): d3explst = begin
  case+ d23es of
  | cons (d23e, d23es) => let
      val d3e: d3exp = case+ d23e of
        | D23Ed2exp d2e => d2exp_tr_up d2e | D23Ed3exp d3e => d3e
    in
      cons (d3e, d23explst_tr_up d23es)
    end
  | nil () => nil ()
end // end of [d23explst_tr_up]

fn d23explst_tr_dn {n:nat}
  (loc0: loc_t, d23es: d23explst, s2es: s2explst n)
  : d3explst n = let
  fun aux {n:nat}
    (d23es: list (d23exp, n), s2es: s2explst n)
    : d3explst n = begin case+ d23es of
    | cons (d23e, d23es) => let
        val+ cons (s2e, s2es) = s2es
        val s2e = un_s2exp_refarg_arg s2e
        val d3e = case+ d23e of
          | D23Ed2exp d2e => d2exp_tr_dn (d2e, s2e)
          | D23Ed3exp d3e => (d3exp_tr_dn (d3e, s2e); d3e)
      in
        cons (d3e, aux (d23es, s2es))
      end
    | nil () => nil ()
    end // end of [aux]
  val [sgn:int] sgn = $Lst.list_length_compare (d23es, s2es)
  val () = (
    if sgn <> 0 then begin
      prerr loc0;
      prerr ": error(3)";
      $Deb.debug_prerrf (": %s: d23explst_tr_dn", @(THISFILENAME));
      if sgn > 0 then prerr ": arity mismatch: less arguments are needed.";
      if sgn < 0 then prerr ": arity mismatch: more arguments are needed.";
      prerr_newline ();
      $Err.abort {void} ();
      assert (sgn = 0) // deadcode
    end else begin
      () // [sgn = 0] holds!
    end
  ) : [sgn==0] void
in
  aux (d23es, s2es)
end // end of [d23explst_tr_dn]

fun d2explst_arg_tr_up (d2es: d2explst): d23explst = begin case+ d2es of
  | cons (d2e, d2es) => let
      val d23e: d23exp = begin
        if d2exp_is_varlamcst d2e then D23Ed2exp d2e else D23Ed3exp (d2exp_tr_up d2e)
      end
    in
      cons (d23e, d2explst_arg_tr_up d2es)
    end
  | nil () => nil ()
end // end of [d2explst_arg_tr_up]

fun d23explst_open_and_add (d23es: d23explst): void = begin
  case+ d23es of
  | cons (d23e, d23es) => let
      val () = case+ d23e of
        | D23Ed2exp d2e => () | D23Ed3exp d3e => d3exp_open_and_add d3e
    in
      d23explst_open_and_add d23es
    end
  | nil () => ()
end // end of [d23explst_open_and_add]

(* ****** ****** *)

fn d23exp_app_tr_up
  (d3e_fun: d3exp, loc_arg: loc_t, npf: int, d23es_arg: d23explst)
  : d3exp = let
(*
  val () = begin
    prerr "d23exp_app_tr_up: d3e_fun.d3exp_typ = ";
    prerr d3e_fun.d3exp_typ;
    prerr_newline ()
  end
*)
  val loc_fun = d3e_fun.d3exp_loc
  val s2e_fun = s2exp_uni_instantiate_all (loc_fun, d3e_fun.d3exp_typ)
  val () = d3exp_typ_set (d3e_fun, s2e_fun)
(*
  val () = begin
    prerr "d23exp_app_tr_up: s2e_fun = "; prerr s2e_fun; prerr_newline ()
  end
*)
in
  case+ s2e_fun.s2exp_node of
  | S2Efun (
      fc, _(*lin*), s2fe_fun, npf_fun, s2es_fun_arg, s2e_fun_res
    ) => let
(*
      val () = begin
        prerr "d23exp_app_tr_up: s2fe_fun = "; prerr s2fe_fun; prerr_newline ()
      end
      val () = begin
        prerrf ("d23exp_app_tr_up: npf = %i and npf_fun = %i", @(npf, npf_fun));
        prerr_newline ()
      end
*)
      val loc_app = $Loc.location_combine (loc_fun, loc_arg)
      val () = pfarity_check_fun (loc_fun, npf_fun, npf)
      val d3es_arg = d23explst_tr_dn (loc_arg, d23es_arg, s2es_fun_arg)
      val s2e_fun_res = s2exp_whnf s2e_fun_res
      var s2e_res: s2exp = s2e_fun_res
      var wths2es: wths2explst = WTHS2EXPLSTnil ()
      val iswth = s2exp_is_wth s2e_fun_res
      val () =
        if iswth then let
          val s2e_fun_res = s2exp_opnexi_and_add (loc_app, s2e_fun_res)
        in
          case+ s2e_fun_res.s2exp_node of
          | S2Ewth (s2e, wths2es1) => (s2e_res := s2e; wths2es := wths2es1)
          | _ => $Err.error ("Deadcode: d23exp_app_tr_up: iswth")
        end
      val d3e_fun = d3exp_funclo_restore (fc, d3e_fun)
      val d3es_arg = (
        if iswth then d3explst_arg_restore (d3es_arg, wths2es) else d3es_arg
      ) : d3explst
      val () = the_effect_env_check_seff (loc_app, s2fe_fun)
    in
      d3exp_app_dyn (loc_app, s2e_res, s2fe_fun, d3e_fun, npf, d3es_arg)
    end
  | S2EVar s2V_fun => let
      val d3es_arg = d23explst_tr_up d23es_arg
      val s2es_arg = aux (npf, d3es_arg) where {
        fun aux {n:nat} (i: int, d3es: d3explst n)
          :<cloptr1> s2explst n = begin case+ d3es of
          | cons (d3e, d3es) => let
              val s2e = d3e.d3exp_typ; val s2t = s2e.s2exp_srt
              val s2t_arg: s2rt =
                if i > 0 then
                  (if s2rt_is_linear s2t then s2rt_view else s2rt_prop)
                else s2t
              val s2e_arg = s2exp_Var_make_srt (loc_fun, s2t_arg)
              val () = $SOL.s2exp_tyleq_solve (d3e.d3exp_loc, s2e, s2e_arg)
            in
              cons (s2e_arg, aux (i-1, d3es))
            end
          | nil () => nil ()
        end // end of [aux]
      } // end of [where]
      val s2e_res = s2exp_Var_make_srt (loc_fun, s2rt_t0ype)
      val s2fe = S2EFFall ()
      val s2e = s2exp_fun_srt (
        s2rt_type, $Syn.FUNCLOfun (), 0(*lin*), s2fe, npf, s2es_arg, s2e_res
      ) // end of [s2exp_fun_srt]
      val () = $SOL.s2exp_equal_solve (loc_fun, s2e_fun, s2e)
      val loc_app = $Loc.location_combine (loc_fun, loc_arg)
    in
      d3exp_app_dyn (loc_app, s2e_res, s2fe, d3e_fun, npf, d3es_arg)
    end
  | _ => begin
      prerr loc_fun;
      prerr ": error(3)";
      $Deb.debug_prerrf (": %s: d23exp_app_tr_dn", @(THISFILENAME));
      prerr ": the dynamic expression is applied but its type is [";
      prerr s2e_fun;
      prerr "].";
      prerr_newline ();
      $Err.abort {d3exp} ()
    end
end // end of [d23exp_app_tr_up]

(* ****** ****** *)

fun d2exp_apps_tr_up (d3e_fun: d3exp, d2as: d2exparglst): d3exp =
  case+ d2as of
  | cons (d2a, d2as) => begin case+ d2a of
    | D2EXPARGsta (s2as) => begin
        d2exp_apps_sta_tr_up (d3e_fun, s2as, d2as)
      end // end of [D2EXPARGsta]
    | D2EXPARGdyn (loc_arg, npf, d2es_arg) => begin
        d2exp_apps_dyn_tr_up (d3e_fun, loc_arg, npf, d2es_arg, d2as)
      end // end of [D2EXPARGdyn]
    end // end of [cons]
  | nil () => d3e_fun
// end of [d2exp_apps_tr_up]

and d2exp_apps_sta_tr_up
  (d3e_fun: d3exp, s2as: s2exparglst, d2as: d2exparglst): d3exp = let
  val () = d3exp_open_and_add d3e_fun
  val s2e_fun = d3e_fun.d3exp_typ
  val loc_app = aux (d3e_fun.d3exp_loc, s2as) where {
    fun aux (loc: loc_t, s2as: s2exparglst): loc_t = case+ s2as of
      | cons (s2a, s2as) => begin case+ s2as of
        | nil _ => $Loc.location_combine (loc, s2a.s2exparg_loc)
        | cons _ => aux (loc, s2as)
        end
      | _ => loc
  } // end of where
  val s2e_fun = s2exp_uni_instantiate_sexparglst (loc_app, s2e_fun, s2as)
  val d3e_fun = d3exp_app_sta (loc_app, s2e_fun, d3e_fun)
in
  d2exp_apps_tr_up (d3e_fun, d2as)
end // end of [d2exp_apps_sta_tr_up]

and d2exp_apps_dyn_tr_up
  (d3e_fun: d3exp,
   loc_arg: loc_t, npf: int, d2es_arg: d2explst, d2as: d2exparglst)
  : d3exp = let
  val loc_app = $Loc.location_combine (d3e_fun.d3exp_loc, loc_arg)
  val () = d3exp_open_and_add d3e_fun; val s2e_fun = d3e_fun.d3exp_typ
in
  case+ s2e_fun.s2exp_node of
(*
  | S2EVar s2V_fun => let
      val d3es_arg = d2explst_tr_up d2es_arg
      val () = d3explst_open_and_add d3es_arg
      val s2es_arg = d3explst_typ_get d3es_arg
      val s2e_res = s2exp_Var_make_srt (loc_app, srt2_t0ype)
      val s2e_fun_new = s2exp_fun_srt
        (s2rt_type, Syn.FUNCLOfun (), S2EFFall (), npf, s2es_arg, s2e_res)
      val () = $SOL.s2exp_tyleq_solve (loc_app, s2e_fun, s2e_fun_new)
      val () = the_effect_env_check_all (loc_app)
      val d3e_fun = d3exp_app_dyn
        (loc_app, s2e_res, S2EFFall (), d3e_fun, npf, d3es_arg)
    in
      d2exp_apps_tr_up (d3e_fun, d2as)
    end
*)
  | _ => let
      val d23es_arg = d2explst_arg_tr_up d2es_arg
      val () = d23explst_open_and_add d23es_arg
      val d3e_fun = d23exp_app_tr_up (d3e_fun, loc_arg, npf, d23es_arg)
    in
      d2exp_apps_tr_up (d3e_fun, d2as)
    end
end // end of [d2exp_apps_dyn_tr_up]

(* ****** ****** *)

local

datatype d3exparg = 
  | D3EXPARGsta of s2exparglst
  | D3EXPARGdyn of (loc_t(*arg*), int(*npf*), d3explst)

typedef d3exparglst = List d3exparg

//

typedef xyz_t = @(d3exp, s2kexp, int)
typedef xyzlst_t = List xyz_t

fn fprint_xyz {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, xyz: xyz_t)
  : void = begin
  fprint1_string (pf | out, "(");
  fprint_d3exp (pf | out, xyz.0);
  fprint1_string (pf | out, ", ");
  fprint_s2kexp (pf | out, xyz.1);
  fprint1_string (pf | out, ", ");
  fprint1_int (pf | out, xyz.2);
  fprint1_string (pf | out, ")")
end

fn print_xyz (xyz: xyz_t): void = print_mac (fprint_xyz, xyz)
fn prerr_xyz (xyz: xyz_t): void = prerr_mac (fprint_xyz, xyz)

//

fn fprint_xyz_root {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, xyz: xyz_t)
  : void = let
  fun aux (d3e: d3exp): d3exp = case+ d3e.d3exp_node of
    | D3Eapp_dyn (d3e_fun, _(*npf*), _(*d3es_arg*)) => aux (d3e_fun)
    | D3Eapp_sta (d3e) => aux (d3e)
    | _ => d3e
  val d3e = aux (xyz.0)
in
  case+ d3e.d3exp_node of
  | D3Ecst d2c => begin
      fprint_d2cst (pf | out, d2c)
    end
  | D3Evar d2v => begin
      fprint_d2var (pf | out, d2v)
    end
  | _ => begin
      fprint1_string (pf | out, "Internal Error: fprint_xyz_root: d3e = ");
      fprint_d3exp (pf | out, d3e);
      fprint_newline (pf | out);
      $Err.abort ()
    end
end // end of [fprint_xyz_root]

fn print_xyz_root (xyz: xyz_t): void = print_mac (fprint_xyz_root, xyz)
fn prerr_xyz_root (xyz: xyz_t): void = prerr_mac (fprint_xyz_root, xyz)

(* ****** ****** *)

fn d2exp_item_tr_up (loc0: loc_t, d2i: d2item): d3exp = begin
  case+ d2i of
  | D2ITEMcst d2c => d2exp_cst_tr_up (loc0, d2c)
  | D2ITEMvar d2v => d2exp_var_tr_up (loc0, d2v)
  | _ => begin
      prerr loc0;
      prerr ": error(3)";
      $Deb.debug_prerrf (": %s: d2exp_item_tr_up", @(THISFILENAME));
      prerr ": the dynamic expression needs to be a constant or a variable.";
      prerr_newline ();
      $Err.abort {d3exp} ()
    end
end // end of [d2exp_item_tr_up]

fun s2kexplst_make_d3explst (d3es: d3explst): s2kexplst = begin
  case+ d3es of
  | cons (d3e, d3es) => begin
      cons (s2kexp_make_s2exp d3e.d3exp_typ, s2kexplst_make_d3explst d3es)
    end
  | nil () => nil ()
end // end of [s2kexplst_make_d3explst]

fun aux_filter
  (xyzs: xyzlst_t, s2kes: s2kexplst): xyzlst_t = let
in
  case+ xyzs of
  | cons (xyz, xyzs) => let
(*
      val () = begin
        prerr "aux_filter: xyz = "; prerr_xyz xyz; prerr_newline ()
      end
*)
    in
      case+ s2kexp_match_fun_arg (xyz.1, s2kes) of
      | ~Some_vt s2keapprox => let
          val approx = xyz.2 + s2keapprox.1
          val xyz_new = @(xyz.0, s2keapprox.0, approx)
(*
          val () = begin
            prerr "aux_filter: xyz_new = "; prerr_xyz xyz_new; prerr_newline ()
          end
*)
        in
          xyz_new :: aux_filter (xyzs, s2kes)
        end
      | ~None_vt () => aux_filter (xyzs, s2kes)
    end
  | nil () => nil ()
end // end of [aux_filter]


fun aux_select0 (xyzs: xyzlst_t): xyzlst_t = begin case+ xyzs of
  | cons (xyz, xyzs) => begin
      if xyz.2 > 0 then aux_select0 xyzs else cons (xyz, aux_select0 xyzs)
    end
  | nil () => nil ()
end // end of [aux_select0]

fun aux1
  (loc0: loc_t, d3e_fun: d3exp, d3as: d3exparglst, d2as: d2exparglst)
  : d3exp = begin case+ d3as of
  | cons (d3a, d3as) => begin case+ d3a of
    | D3EXPARGsta s2as => let
        val s2e_fun = begin
          s2exp_uni_instantiate_sexparglst (loc0, d3e_fun.d3exp_typ, s2as)
        end
        val d3e_fun = d3exp_app_sta (loc0, s2e_fun, d3e_fun)
      in
        aux1 (loc0, d3e_fun, d3as, d2as)
      end
    | D3EXPARGdyn (loc_arg, npf, d3es_arg) => let
        val () = d3explst_open_and_add d3es_arg
        val s2es_arg = d3explst_typ_get d3es_arg
        val s2e_fun = s2exp_uni_instantiate_all (loc0, d3e_fun.d3exp_typ)
        val () = d3exp_typ_set (d3e_fun, s2e_fun)
(*
        val () = begin
          prerr "d2exp_apps_sym_tr_up: aux1: s2e_fun = ";
          prerr s2e_fun;
          prerr_newline ()
        end
        val () = begin
          prerr "d2exp_apps_sym_tr_up: aux1: s2es_arg = ";
          prerr s2es_arg;
          prerr_newline ()
        end
*)
      in
        case+ s2e_fun.s2exp_node of
        | S2Efun (fc, _(*lin*), s2fe_fun, npf_fun, s2es_fun_arg, s2e_fun_res) => let
            val () = pfarity_check_fun (loc0, npf_fun, npf)
            val () = $SOL.s2explst_arg_tyleq_solve (loc_arg, s2es_arg, s2es_fun_arg)
            var s2e_res: s2exp = s2e_fun_res
            var wths2es: wths2explst = WTHS2EXPLSTnil ()
            val iswth = s2exp_is_wth s2e_fun_res
            val () =
              if iswth then let
                val s2e_fun_res = s2exp_opnexi_and_add (loc0, s2e_fun_res)
              in
                case+ s2e_fun_res.s2exp_node of
                | S2Ewth (s2e, wths2es1) => (s2e_res := s2e; wths2es := wths2es1)
                | _ => $Err.error ("Deadcode: d2exp_apps_sym_tr_up: aux1: iswth")
              end
            val d3e_fun = d3exp_funclo_restore (fc, d3e_fun)
            val d3es_arg = (
              if iswth then d3explst_arg_restore (d3es_arg, wths2es) else d3es_arg
            ) : d3explst
            val () = the_effect_env_check_seff (loc0, s2fe_fun)
            val d3e_fun =
              d3exp_app_dyn (loc0, s2e_res, s2fe_fun, d3e_fun, npf, d3es_arg)
          in
            aux1 (loc0, d3e_fun, d3as, d2as)
          end
        | _ => begin
            $Loc.prerr_location loc0;
            prerr ": error(3)";
            $Deb.debug_prerrf (": %s: d2exp_apps_sym_tr_up: aux1", @(THISFILENAME));
            prerr ": the dynamic expression is applied but its type is [";
            prerr s2e_fun;
            prerr "].";
            prerr_newline ();
            $Err.abort {d3exp} ()
          end
      end // end of [let]
    end // end of [begin]
  | nil () => d2exp_apps_tr_up (d3e_fun, d2as)
end // end of [aux1]

fun aux2
  (loc0: loc_t, d2s: d2sym, d3as: d3exparglst,
   xyzs: xyzlst_t, d2as: d2exparglst): d3exp = let
  fn err_nil (loc0: loc_t, d2s: d2sym):<cloref1> d3exp = begin
     $Loc.prerr_location loc0;
     prerr ": error(3)";
     $Deb.debug_prerrf (": %s: d2exp_apps_sym_tr_up: aux2", @(THISFILENAME));
     prerr ": the symbol [";
     prerr d2s;
     prerr "] cannot be resolved: there is no match.";
     prerr_newline ();
     $Err.abort {d3exp} ()
  end // end of [err_nil]
  fn err_cons_cons
     (loc0: loc_t, d2s: d2sym, xyz1: xyz_t, xyz2: xyz_t)
     :<cloref1> d3exp = begin
     $Loc.prerr_location loc0;
     prerr ": error(3)";
     $Deb.debug_prerrf (": %s: d2exp_apps_sym_tr_up: aux2", @(THISFILENAME));
     prerr ": the symbol [";
     prerr d2s;
     prerr "] cannot be resolved: there are too many matches: ";
     prerr_xyz_root xyz1;
     prerr ", ";
     prerr_xyz_root xyz2;
     prerr ", ...";
     prerr_newline ();
     $Err.abort {d3exp} ()
  end // end of [err_cons_cons]
in
  case+ xyzs of
  | cons (xyz, xyzs1) => begin case+ xyzs1 of
    | nil () => begin
        aux1 (loc0, xyz.0, $Lst.list_reverse d3as, d2as)
      end
    | cons _ => begin case+ d2as of
      | nil () => let
          val xyzs = aux_select0 xyzs
        in
          case+ xyzs of
          | cons (xyz, nil ()) => begin 
              aux1 (loc0, xyz.0, $Lst.list_reverse d3as, nil ())
            end
          | nil _ => err_nil (loc0, d2s)
          | cons (xyz1, cons (xyz2, _)) => begin
              err_cons_cons (loc0, d2s, xyz1, xyz2)
            end
        end // end of [let]
      | cons (d2a, d2as) => begin case+ d2a of
        | D2EXPARGsta s2as => let
            val d3a = D3EXPARGsta s2as
          in
            aux2 (loc0, d2s, d3a :: d3as, xyzs, d2as)
          end
        | D2EXPARGdyn (loc_arg, npf, d2es) => let
            val d3es = d23explst_tr_up (d2explst_arg_tr_up d2es)
(*
            val () = begin
              prerr "d2exp_apps_sym_tr_up: aux2: s2es = ";
              prerr (d3explst_typ_get d3es); prerr_newline ()
            end
*)
            val d3a = D3EXPARGdyn (loc_arg, npf, d3es)
            val xyzs = aux_filter (xyzs, s2kexplst_make_d3explst d3es)
          in
            aux2 (loc0, d2s, d3a :: d3as, xyzs, d2as)
          end // end of [D2EXPARGdyn]
        end // end of [cons (d2a, d2as)]
      end // end of [cons _]
    end // end of [cons (xyz, xyzs1)]
  | nil () => err_nil (loc0, d2s)
end // end of [aux2]

fn* aux3 (d2as: d2exparglst, s2e: s2exp): bool = begin
  case+ d2as of
  | cons (d2a, d2as) => begin case+ d2a of
    | D2EXPARGdyn (_(*loc*), npf, d2es) => aux3_app (npf, d2es, d2as, s2e)
    | D2EXPARGsta _ => aux3 (d2as, s2e)
    end
  | nil () => true
end // end of [aux3]

and aux3_app
  (npf: int, d2es: d2explst, d2as: d2exparglst, s2e: s2exp): bool = let
  val s2e = s2exp_whnf (s2e)
in
  case+ s2e.s2exp_node of
  | S2Efun (_(*fc*), _(*lin*), _(*eff*), npf1, s2es_arg, s2e_res) => begin
      if (npf = npf1) then
        if $Lst.list_length_compare (d2es, s2es_arg) = 0 then aux3 (d2as, s2e_res)
        else false
      else false
    end // end of [S2Efun]
  | S2Eexi (_(*s2vs*), _(*s2ps*), s2e) => aux3_app (npf, d2es, d2as, s2e)
  | S2Euni (_(*s2vs*), _(*s2ps*), s2e) => aux3_app (npf, d2es, d2as, s2e)
  | S2Emetfn (_(*stamp*), _(*met*), s2e) => aux3_app (npf, d2es, d2as, s2e)
  | _ => false
end // end of [aux3_app]

in // in of [local]

fn d2exp_apps_sym_tr_up
  (loc0: loc_t, d2s: d2sym, d2as: d2exparglst): d3exp = let
(*
  val () = begin
    prerr "d2exp_apps_sym_tr_up: d2s = ";
    prerr d2s;
    prerr_newline ()
  end
  val () = begin
    prerr "d2exp_apps_sym_tr_up: d2s.d2sym_itm = ";
    prerr d2s.d2sym_itm;
    prerr_newline ()
  end
*)
  val xyzs =
    aux (loc0, d2as, d2s.d2sym_itm, list_vt_nil ()) where {
    viewtypedef d2itemlstlst_vt = List_vt (d2itemlst)
    fun aux (
        loc0: loc_t
      , d2as: d2exparglst, d2is: d2itemlst, d2iss: d2itemlstlst_vt
      ) : xyzlst_t = begin case+ d2is of
      | cons (d2i, d2is) => begin case+ d2i of
        | D2ITEMsym (d2is_new) => begin
            aux (loc0, d2as, d2is_new, list_vt_cons (d2is, d2iss))
          end
        | _ => let
            val d3e = d2exp_item_tr_up (loc0, d2i); val s2e = d3e.d3exp_typ
          in
            if aux3 (d2as, s2e) then let
              val s2ke = s2kexp_make_s2exp (s2e)
            in
              @(d3e, s2ke, 0) :: aux (loc0, d2as, d2is, d2iss)
            end else begin
              aux (loc0, d2as, d2is, d2iss)
            end
          end
        end // end of [cons]
      | nil () => begin case+ d2iss of
        | ~list_vt_cons (d2is, d2iss) => aux (loc0, d2as, d2is, d2iss)
        | ~list_vt_nil () => nil ()
        end // end of [nil]
      end // end of [aux]
  } // end of [where]
in
  aux2 (loc0, d2s, nil (), xyzs, d2as)
end // end of [d2exp_apps_sym_tr_up]

end // end of [local]

(* ****** ****** *)

extern fun d2exp_viewat_assgn_tr_up
  (loc0: loc_t, d2e_l: d2exp, d2e_r: d2exp): d3exp

fn d2exp_assgn_tr_up
  (loc0: loc_t, d2e_l: d2exp, d2e_r: d2exp): d3exp = let
  val l2val = l2val_make_d2exp d2e_l
in
  case+ l2val of
  | L2VALarrsub (d2s_brackets, d2e_arr, loc_ind, d2ess_ind) => begin
    case+ d2ess_ind of
    | cons (d2es_ind, nil ()) => let
        val loc_arg = $Loc.location_combine (d2e_arr.d2exp_loc, d2e_r.d2exp_loc)
        val d2es_arg = cons (d2e_arr, $Lst.list_extend (d2es_ind, d2e_r))
        val d2a = D2EXPARGdyn (loc_arg, 0, d2es_arg)
      in
        d2exp_apps_sym_tr_up (loc_arg, d2s_brackets, '[d2a])
      end
    | _ => begin
        prerr loc0; prerr ": error(3)";
        prerr ": the format for array subscripts ["; prerr d2ess_ind;
        prerr "] is not supported."; prerr_newline ();
        $Err.abort {d3exp} ()
      end
    end // end of [L2VALarrsub]
  | L2VALptr (d2e0, d2ls) => let
(*
      val () = begin
        prerr "d2exp_assgn_tr_up: L2VALptr: d2e0 = "; prerr d2e0; prerr_newline ()
      end
*)
      val d3e0 = d2exp_tr_up d2e0
      val () = d3exp_open_and_add d3e0
      val s2e0 = d3e0.d3exp_typ
(*
      val () = begin
        prerr "d2exp_assgn_tr_up: L2VALptr: s2e0 = "; prerr s2e0; prerr_newline ()
      end
*)
    in
      case+ un_s2exp_ptr_addr_type s2e0 of
      | ~Some_vt s2e_addr => let
          val d3ls_nt = d2lablst_tr_up d2ls
          val s2ls_nt = s2lab0lst_of_d3lab0lst d3ls_nt
          val d3e_r = d2exp_tr_up d2e_r
          val () = d3exp_open_and_add d3e_r
          val s2e_r = d3e_r.d3exp_typ
          val s2ls = s2exp_addr_slablst_assgn (loc0, s2e_addr, s2ls_nt, s2e_r)
(*
          val sgn = $Lst.list_length_compare (s2ls, s2ls_nt)
          val () =
            if (sgn <> 0) then begin
              prerr "Internal Error: d2exp_assgn_tr_up: list length mismatch!";
              prerr_newline ();
              $Err.abort {void} ()
            end
*)
          val d3ls = d3lab1lst_of_d3lab0lst_s2lablst (d3ls_nt, s2ls)
        in
          d3exp_assgn_ptr (loc0, d3e0, d3ls, d3e_r)
        end // end of [Some_vt]
      | ~None_vt () => begin case+ d2ls of
        | nil () => begin case+ un_s2exp_ref_viewt0ype_type s2e0 of
          | ~Some_vt s2e_elt => let
              val () = the_effect_env_check_ref (loc0) // write to a reference is effectful
              val () = // linearity checking
                if s2exp_is_linear s2e_elt then begin
                  prerr d2e0.d2exp_loc;
                  prerr ": error(3)";
                  prerr ": a reference to a linear value cannot be updated directly.";
                  prerr_newline ();
                  $Err.abort {void} ()
                end
              val d3e_r = d2exp_tr_dn (d2e_r, s2e_elt)
            in
              d3exp_assgn_ptr (loc0, d3e0, nil (), d3e_r)
            end
          | ~None_vt () => begin
              prerr d2e0.d2exp_loc;
              prerr ": error(3)";
              prerr ": the dynamic expression is expected to be a pointer or reference";
              prerr ", but it is assigned the type ["; prerr s2e0; prerr "]";
              prerr_newline ();
              $Err.abort {d3exp} ()
            end
          end
        | cons _ => begin
            prerr d2e0.d2exp_loc;
            prerr ": error(3)";
            prerr ": the dynamic expression is expected to be a pointer";
            prerr ", but it is assigned the type ["; prerr s2e0; prerr "]";
            prerr_newline ();
            $Err.abort {d3exp} ()
          end
        end // end of [None_vt]
      // end of [case]
    end
  | L2VALvar_lin (d2v, d2ls) => let
      val d3ls_nt = d2lablst_tr_up d2ls
      val s2ls_nt = s2lab0lst_of_d3lab0lst d3ls_nt
      val d3e_r = d2exp_tr_up d2e_r
      val () = d3exp_open_and_add d3e_r
      val s2e_r = d3e_r.d3exp_typ
      val () =
        if s2exp_is_proof s2e_r then () else begin
          prerr d2e_l.d2exp_loc;
          prerr ": error(3)";
          prerr ": the linear dynamic variable ["; prerr d2v;
          prerr "] can support proof assignment but not value assignment.";
          prerr_newline ();
          $Err.abort {void} ()
        end
      val s2ls = begin
        d2var_lin_slablst_assgn (loc0, d2v, s2ls_nt, s2e_r)
      end
      val d3ls = d3lab1lst_of_d3lab0lst_s2lablst (d3ls_nt, s2ls)
    in
      d3exp_assgn_var (loc0, d2v, d3ls, d3e_r)
    end
  | L2VALvar_mut (d2v, d2ls) => let
      val d3ls_nt = d2lablst_tr_up d2ls
      val s2ls_nt = s2lab0lst_of_d3lab0lst d3ls_nt
      val d3e_r = d2exp_tr_up d2e_r
      val () = d3exp_open_and_add d3e_r
      val s2ls = begin
        d2var_mut_slablst_assgn (loc0, d2v, s2ls_nt, d3e_r.d3exp_typ)
      end
      val d3ls = d3lab1lst_of_d3lab0lst_s2lablst (d3ls_nt, s2ls)
    in
      d3exp_assgn_var (loc0, d2v, d3ls, d3e_r)
    end
  | L2VALnone d2e_l => begin case+ d2e_l.d2exp_node of
    | D2Eviewat d2e1_l => d2exp_viewat_assgn_tr_up (loc0, d2e1_l, d2e_r)
    | _ => begin
        prerr loc0;
        prerr ": the dynamic expression is expected to be a left-value";
        prerr ", but it is not.";
        prerr_newline ();
        $Err.abort {d3exp} ()
      end
    end // end of [L2VALnone]
  // end of [case]
end // end of [d2exp_assgn_tr_up]

(* ****** ****** *)

fn d3exp_s2exp_lazy_force_tr_up
  (loc0: loc_t, d3e0: d3exp, s2e0: s2exp): d3exp =
  case+ un_s2exp_lazy_t0ype_type s2e0 of
  | ~Some_vt (s2e_elt) => d3exp_lazy_force (loc0, s2e_elt, 0(*lin*), d3e0)
  | ~None_vt () => begin case+ un_s2exp_lazy_viewt0ype_viewtype s2e0 of
    | ~Some_vt (s2e_elt) => d3exp_lazy_force (loc0, s2e_elt, 1(*lin*), d3e0)
    | ~None_vt () => begin
        prerr d3e0.d3exp_loc; prerr ": error(3)";
        prerr ": the dynamic expression is assigned the type ["; prerr s2e0;
        prerr "], but a pointer, reference, or delayed computation is expected.";
        prerr_newline ();
        $Err.abort {d3exp} ()
      end // end of [None_vt]
    end // end of [None_vt]
// end of [d3exp_s2exp_lazy_force_tr_up]

fn d2exp_deref_tr_up
  (loc0: loc_t, d2e0: d2exp, d2ls: d2lablst): d3exp = let
(*
  val () = begin
    prerr "d2exp_deref_tr_up: d2e0 = "; prerr d2e0; prerr_newline ();
  end
*)
  val d3e0 = d2exp_tr_up d2e0
  val () = d3exp_open_and_add d3e0
  val s2e0 = d3e0.d3exp_typ
(*
  val () = begin
    prerr "d2exp_deref_tr_up: s2e0 = "; prerr s2e0; prerr_newline ();
  end // end of [val]
*)
in
  case+ un_s2exp_ptr_addr_type s2e0 of
  | ~Some_vt s2e_addr => let
      val d3ls_nt = d2lablst_tr_up d2ls
      val s2ls_nt = s2lab0lst_of_d3lab0lst d3ls_nt
      val (s2e_elt, s2ls) = s2exp_addr_slablst_deref (loc0, s2e_addr, s2ls_nt)
(*
      val () = begin
        prerr "d2exp_deref_tr_up: s2e_elt = "; prerr s2e_elt; prerr_newline ()
      end
      val [sgn:int] sgn = $Lst.list_length_compare (s2ls, s2ls_nt)
      val () [sgn==0] void =
        if (sgn <> 0) then begin
          prerr "Internal Error: d2exp_deref_tr_up: list length mismatch!";
          prerr_newline ();
          $Err.abort {void} ();
          assert (sgn = 0) // deadcode
        end else begin
          () // [sgn = 0] holds!
        end
*)
      val d3ls = d3lab1lst_of_d3lab0lst_s2lablst (d3ls_nt, s2ls)
    in
      d3exp_sel_ptr (loc0, s2e_elt, d3e0, d3ls)
    end // end of [Some_vt]
  | ~None_vt () => begin case+ d2ls of
    | nil () => begin case+ un_s2exp_ref_viewt0ype_type s2e0 of
      | ~Some_vt s2e_elt => let
          val () = the_effect_env_check_ref (loc0) // read from a reference is effectful
          val () = // linearity checking
            if s2exp_is_linear s2e_elt then begin
              prerr d2e0.d2exp_loc;
              prerr ": error(3)";
              prerr ": a reference to a linear value cannot be accessed directly.";
              prerr_newline ();
              $Err.abort {void} ()
            end // end of [if]
        in
          d3exp_sel_ptr (loc0, s2e_elt, d3e0, nil ())
        end // end of [Some_vt]
      | ~None_vt () => d3exp_s2exp_lazy_force_tr_up (loc0, d3e0, s2e0)
      end // end of [nil]
    | cons _ => begin
        prerr d2e0.d2exp_loc;
        prerr ": error(3)";
        prerr ": the dynamic expression is expected to be a pointer";
        prerr ", but it is assigned the type ["; prerr s2e0; prerr "]";
        prerr_newline ();
        $Err.abort {d3exp} ()
      end // end of [cons]
    end // end of [None_vt]
  // end of [case]
end // end of [d2exp_deref_tr_up]

(* ****** ****** *)

fn d2exp_con_tr_up
  (loc0: loc_t, d2c: d2con_t, s2as: s2exparglst, npf: int, d2es: d2explst)
  : d3exp = let
  val d23es = d2explst_arg_tr_up d2es
  val () = d23explst_open_and_add d23es
  val s2e_d2c = d2con_typ_get d2c
  val s2e = s2exp_uni_instantiate_sexparglst (loc0, s2e_d2c, s2as)
  val s2e = s2exp_uni_instantiate_all (loc0, s2e)
in
  case+ s2e.s2exp_node of
  | S2Efun (
      _(*fc*), _(*lin*), _(*s2fe*), npf_fun, s2es_fun_arg, s2e_fun_res
    ) => let
      val () = pfarity_check_fun (loc0, npf_fun, npf)
      val d3es = d23explst_tr_dn (loc0, d23es, s2es_fun_arg)
    in
      d3exp_con (loc0, s2e_fun_res, d2c, npf, d3es)
    end
  | _ => begin
      prerr loc0;
      prerr ": error(3)";
      $Deb.debug_prerrf (": %s: d2exp_con_tr_up", @(THISFILENAME));
      prerr ": the dynamic constructor [";
      prerr d2c;
      prerr "] is applied but its type [";
      prerr s2e_d2c;
      prerr "] indicates that it should not be.";
      prerr_newline ();
      $Err.abort {d3exp} ()
    end
end // end [d2exp_con_tr_up]

(* ****** ****** *)

fn d2exp_decrypt_tr_up
  (loc0: loc_t, d2e: d2exp): d3exp = let
  val d3e = d2exp_tr_up d2e
  val s2e_crypt = d3e.d3exp_typ
  val s2e = case+ s2e_crypt.s2exp_node of
    | S2Ecrypt s2e => s2e | _ => begin
        prerr loc0;
        prerr ": error(3)";
        prerr ": the dynamic expression is expected to be crypted";
        prerr ", but it is assigned the type ["; prerr s2e_crypt; prerr "].";
        $Err.abort {s2exp} ()
      end
in
  d3exp_crypt (loc0, s2e, ~1(*decrypt*), d3e)
end

fn d2exp_encrypt_tr_up
  (loc0: loc_t, d2e: d2exp): d3exp = let
  val d3e = d2exp_tr_up d2e
  val s2e = s2exp_crypt d3e.d3exp_typ
in
  d3exp_crypt (loc0, s2e,  1(*encrypt*), d3e)
end

fn d2exp_crypt_tr_up
  (loc0: loc_t, knd: int, d2e: d2exp): d3exp = begin
  if knd > 0 then begin
    d2exp_encrypt_tr_up (loc0, d2e)
  end else begin
    d2exp_decrypt_tr_up (loc0, d2e)
  end
end // end of [d2exp_crypt_tr_up]

(* ****** ****** *)

fn d2exp_foldat_freeat_tr_up
  (loc0: loc_t, isfold: bool, s2as: s2exparglst, d2e: d2exp): d3exp = let
  fn aux (loc0: loc_t, s2e_addr: s2exp): s2exp =
    case+ the_d2varset_env_find_viewat (s2e_addr, nil ()) of
    | ~Some_vt ans => (d2var_typ_set (ans.0, None ()); ans.1)
    | ~None_vt () => begin
        prerr loc0;
        prerr ": Internal Error: d2exp_foldat_freeat_tr_up: no view at [";
        prerr s2e_addr; prerr "]."; prerr_newline ();
        $Err.abort {s2exp} ()
      end
  fun auxlst (loc0: loc_t, s2es_addr: s2explst): s2explst =
    case+ s2es_addr of
    | cons (s2e_addr, s2es_addr) =>
        cons (aux (loc0, s2e_addr), auxlst (loc0, s2es_addr))
    | nil () => nil ()
  val d3e = d2exp_tr_up d2e
  val () = d3exp_open_and_add d3e
  val s2e = d3e.d3exp_typ
  var s2es_addr: s2explst = nil ()
  val d2c = case+ s2e.s2exp_node of
    | S2Edatconptr (d2c, s2es) => (s2es_addr := s2es; d2c)
    | _ => begin
        prerr d2e.d2exp_loc;
        prerr ": error(3)";
        if isfold then begin
          prerr ": the dynamic expression cannot be folded as its type is ["
        end else begin
          prerr ": the dynamic expression cannot be freed as its type is ["
        end;
        prerr s2e; prerr "].";
        prerr_newline ();
        $Err.abort {d2con_t} ()
      end // end of [_]
  val s2es_arg = auxlst (loc0, s2es_addr)
  val s2e_d2c = d2con_typ_get (d2c)
  val s2e_d2c = s2exp_uni_instantiate_sexparglst (loc0, s2e_d2c, s2as)
  val s2e_d2c = s2exp_uni_instantiate_all (loc0, s2e_d2c)
  var err: int = 0
  val () = case+ s2e_d2c.s2exp_node of
    | S2Efun (_, _, _, _, s2es_fun_arg, s2e_fun_res) => let
        val s2es_fun_arg = (
          if isfold then s2es_fun_arg else begin
            $Lst.list_map_fun (s2es_fun_arg, s2exp_topize_0)
          end
        ) : s2explst
        val () = begin
          $SOL.s2explst_tyleq_solve_err (loc0, s2es_arg, s2es_fun_arg, err)
        end
(*
        val () = // debugging information
          if isfold then begin
            prerr "d2exp_foldat_tr_up: s2es_fun_arg = ";
            prerr s2es_fun_arg;
            prerr_newline ();
            prerr "d2exp_foldat_tr_up: s2es_arg = ";
            prerr s2es_arg;
            prerr_newline ();
          end else begin
            prerr "d2exp_freeat_tr_up: s2es_fun_arg = ";
            prerr s2es_fun_arg;
            prerr_newline ();
            prerr "d2exp_freeat_tr_up: s2es_arg = ";
            prerr s2es_arg;
            prerr_newline ();
          end
*)
        val () = // error checking
          if err > 0 then begin
            prerr loc0;
            prerr ": error(3)";
            if isfold then begin
              prerr ": argument type mismatch for folding"
            end else begin
              prerr ": argument type mismatch for freeing"
            end;
            prerr_newline ();
            $Err.abort {void} ()
          end
      in
        if isfold then let
          var err: int = 0
          val () = d3exp_lval_typ_set (loc0, 0(*refval*), d3e, s2e_fun_res, err)
        in
          if err > 0 then begin
            prerr loc0;
            prerr ": error(3)";
            prerr ": the dynamic expression needs to be a left-value for folding";
            prerr ", but it is not.";
            prerr_newline ();
            $Err.abort {void} ()
          end
        end
      end
    | _ => begin
        prerr loc0;
        prerr ": Internal Error: d2exp_foldat_freeat_tr_up";
        prerr ": not function type: s2e_d2c = ";
        prerr s2e_d2c; prerr "]."; prerr_newline ();
        $Err.abort {void} ()
      end
in
    if isfold then d3exp_foldat (loc0, d3e) else d3exp_freeat (loc0, d3e)
end

fn d2exp_foldat_tr_up (loc0: loc_t, s2as: s2exparglst, d2e: d2exp): d3exp =
  d2exp_foldat_freeat_tr_up (loc0, true(*isfold*), s2as, d2e)

fn d2exp_freeat_tr_up (loc0: loc_t, s2as: s2exparglst, d2e: d2exp): d3exp =
  d2exp_foldat_freeat_tr_up (loc0, false(*isfold*), s2as, d2e)

(* ****** ****** *)

fn d2exp_ptrof_tr_up (loc0: loc_t, d2e0: d2exp): d3exp = let
  val l2v0 = l2val_make_d2exp d2e0
in
  case+ l2v0 of
  | L2VALptr (d2e_ptr, d2ls) => let
      val d3e_ptr = d2exp_tr_up d2e_ptr
      val () = d3exp_open_and_add d3e_ptr
      val s2e_ptr = d3e_ptr.d3exp_typ
      val s2e_addr =
        case+ un_s2exp_ptr_addr_type s2e_ptr of
        | ~Some_vt s2e => s2e
        | ~None_vt () => begin
            prerr d2e_ptr.d2exp_loc;
            prerr ": error(3)";
            prerr ": the dynamic expression is expected to be a pointer";
            prerr ", but it is assigned the type ["; prerr s2e_ptr; prerr "].";
            prerr_newline ();
            $Err.abort {s2exp} ()
          end
    in
      case+ d2ls of
      | cons _ => let
          val d3ls_nt = d2lablst_tr_up d2ls
          val s2ls_nt = s2lab0lst_of_d3lab0lst d3ls_nt
          val s2ls = begin
            s2exp_addr_viewat_slablst_try (loc0, s2e_addr, s2ls_nt)
          end
          val d3ls = d3lab1lst_of_d3lab0lst_s2lablst (d3ls_nt, s2ls)
          val s2e_prj_addr = s2exp_projlst (s2e_addr, s2ls)
          val s2e_prj_ptr = s2exp_ptr_addr_type (s2e_prj_addr)
        in
          d3exp_ptrof_ptr (loc0, s2e_prj_ptr, d3e_ptr, d3ls)
        end
      | nil () => d3exp_ptrof_ptr (loc0, s2e_ptr, d3e_ptr, nil ())
      // end of [case]
    end // end of [L2VALptr]
  | L2VALvar_mut (d2v, d2ls) => let
      val s2e_addr = d2var_addr_get_some (loc0, d2v)
    in
      case+ d2ls of
      | cons _ => let
          val d3ls_nt = d2lablst_tr_up d2ls
          val s2ls_nt = s2lab0lst_of_d3lab0lst d3ls_nt
          val s2ls = s2exp_addr_viewat_slablst_try (loc0, s2e_addr, s2ls_nt)
          val d3ls = d3lab1lst_of_d3lab0lst_s2lablst (d3ls_nt, s2ls)
          val s2e_prj_addr = s2exp_projlst (s2e_addr, s2ls)
          val s2e_prj_ptr = s2exp_ptr_addr_type (s2e_prj_addr)
        in
          d3exp_ptrof_var (loc0, s2e_prj_ptr, d2v, d3ls)
        end // end of [cons]
      | nil () => let
          val s2e_addr = d2var_addr_get_some (loc0, d2v)
          val s2e_ptr = s2exp_ptr_addr_type (s2e_addr)
        in
          d3exp_ptrof_var (loc0, s2e_ptr, d2v, nil ())
        end // end of [nil]
      // end of [case]
    end // end of [L2VALvar]
  | L2VALarrsub _ => begin
      prerr d2e0.d2exp_loc;
      prerr ": error(3)";
      prerr ": array subscription is not supported for address-of operation.";
      prerr_newline ();
      $Err.abort {d3exp} ()
    end
  | L2VALvar_lin (d2v, _) => begin
      prerr d2e0.d2exp_loc;
      prerr ": error(3)";
      prerr ": the dynamic expression is expected to be a left-value";
      prerr ", but it is not as ["; prerr d2v; prerr "] is not mutable.";
      prerr_newline ();
      $Err.abort {d3exp} ()
    end 
  | L2VALnone _ => begin
      prerr d2e0.d2exp_loc;
      prerr ": error(3)";
      prerr ": the dynamic expression is expected to be a left-value";
      prerr ", but it is not.";
      prerr_newline ();
      $Err.abort {d3exp} ()
    end
end // end of [d2exp_ptrof_tr_up]

(* ****** ****** *)

fn d3exp_nonlin_check (d3e: d3exp): void = begin
  if s2exp_is_linear (d3e.d3exp_typ) then begin
    prerr d3e.d3exp_loc;
    prerr ": error(3)";
    prerr ": the dynamic expression is linear but it should not be.";
    prerr_newline ();
    $Err.abort {void} ()
  end
end // end of [d3exp_sort_check]

fun labd3explst_nonlin_check (ld3es: labd3explst): void = begin
  case+ ld3es of
  | LABD3EXPLSTcons (_(*lab*), d3e, ld3es) => begin
      d3exp_nonlin_check (d3e); labd3explst_nonlin_check (ld3es)
    end
  | LABD3EXPLSTnil () => ()
end // end of [labd3explst_nonlin_check]

fn d2exp_rec_tr_up
  (loc0: loc_t, recknd: int, npf: int, ld2es: labd2explst)
  : d3exp = let
(*
  val () = begin
    prerr "labd2explst_tr_up: ld2es = "; prerr ld2es; prerr_newline ()
  end
*)
  fun aux (ld2es: labd2explst): labd3explst =
    case+ ld2es of
    | LABD2EXPLSTcons (l, d2e, ld2es) => begin
        LABD3EXPLSTcons (l, d2exp_tr_up d2e, aux ld2es)
      end
    | LABD2EXPLSTnil () => LABD3EXPLSTnil ()
  val ld3es = aux ld2es
(*
  val () = begin
    prerr "labd2explst_tr_up: ls2es = "; prerr ls2es; prerr_newline ()
  end
*)
  val () = if recknd = 2 then labd3explst_nonlin_check (ld3es)
  val ls2es = labd3explst_typ_get ld3es
  val s2e_rec = s2exp_tyrec (recknd, npf, ls2es)
in
  d3exp_rec (loc0, s2e_rec, recknd, npf, ld3es)
end // end of [d2exp_rec_tr_up]  

(* ****** ****** *)

fn d3exp_sel_tr_up
  (loc0: loc_t, d3e: d3exp, d3ls_nt: d3lab0lst): d3exp = begin
  case+ d3ls_nt of
  | cons _ => let
      val () = d3exp_open_and_add d3e
      val s2ls_nt = s2lab0lst_of_d3lab0lst d3ls_nt
      var restlin: int = 0 and cstr: s2explst = nil ()
      val @(s2e_prj, s2ls) = begin
        s2exp_slablst_get_restlin_cstr (loc0, d3e.d3exp_typ, s2ls_nt, restlin, cstr)
      end
      val () = // restlin check
        if restlin > 0 then begin
          prerr loc0;
          prerr ": error(3)";
          prerr ": a linear component is abandoned by label selection.";
          prerr_newline ();
          $Err.abort {void} ()
        end
      val () = trans3_env_add_proplst (loc0, cstr)
      val d3ls = d3lab1lst_of_d3lab0lst_s2lablst (d3ls_nt, s2ls)
    in
      d3exp_sel (loc0, s2e_prj, d3e, d3ls)
    end
  | nil () => d3e
end // end of [d3exp_tr_up]

fn d2exp_sel_tr_up
  (loc0: loc_t, d2e0: d2exp, d2ls: d2lablst): d3exp = let
(*
  val () = begin
    prerr "d2exp_sel_tr_up: d2e0 = "; prerr d2e0; prerr_newline ()
  end
*)
in
  case+ d2e0.d2exp_node of
  | D2Evar d2v when d2var_is_mutable d2v => let
      val d3ls_nt = d2lablst_tr_up d2ls
      val s2ls_nt = s2lab0lst_of_d3lab0lst d3ls_nt
      val s2e_addr = d2var_addr_get_some (loc0, d2v)
      val (s2e_elt, s2ls) = s2exp_addr_slablst_deref (loc0, s2e_addr, s2ls_nt)
(*
      val () = begin
        prerr "d2exp_sel_tr_up: s2e_elt = "; prerr s2e_elt; prerr_newline ()
      end
      val [sgn:int] sgn = $Lst.list_length_compare (s2ls, s2ls_nt)
      val (): [sgn==0] void =
        if (sgn <> 0) then begin
          prerr "Internal Error: d2exp_sel_tr_up: list length mismatch!";
          prerr_newline ();
          $Err.abort {void} ();
          assert (sgn = 0) // deadcode
        end else begin
          () // [sgn = 0] holds!
        end
*)
      val d3ls = d3lab1lst_of_d3lab0lst_s2lablst (d3ls_nt, s2ls)
    in
      d3exp_sel_var (loc0, s2e_elt, d2v, d3ls)
    end // end of [D2Evar when d2var_is_mutable]
  | D2Evar d2v when d2var_is_linear d2v => let
      val d3ls_nt = d2lablst_tr_up d2ls
      val s2ls_nt = s2lab0lst_of_d3lab0lst d3ls_nt
      val s2e_d2v = d2var_typ_get_some (loc0, d2v)
      var cstr: s2explst = list_nil ()
      val (s2e_prj, s2e_d2v, s2ls) =
        s2exp_slablst_linget_cstr (loc0, s2e_d2v, s2ls_nt, cstr)
      val () = trans3_env_add_proplst (loc0, cstr)
      val () = d2var_typ_set (d2v, Some s2e_d2v)
      val d3ls = d3lab1lst_of_d3lab0lst_s2lablst (d3ls_nt, s2ls)
    in
      d3exp_sel_var (loc0, s2e_prj, d2v, d3ls)
    end // end of [D2Evar when d2var_is_linear]
  | D2Ederef d2e => d2exp_deref_tr_up (loc0, d2e, d2ls)
  | _ => let
     val d3e0 = d2exp_tr_up d2e0
     val d3ls_nt = d2lablst_tr_up d2ls
   in
     d3exp_sel_tr_up (loc0, d3e0, d3ls_nt)
   end // end of [D2Ederef]
end // end of [d2exp_sel_tr_up]

(* ****** ****** *)

fn d2exp_seq_tr_up
   (loc0: loc_t, d2es: d2explst): d3exp = let
   fun aux (
      d2e: d2exp
    , d2es: d2explst
    , s2e: &(s2exp?) >> s2exp
    , s2e_void: s2exp
    ) : d3explst = begin
    case+ :(s2e: s2exp) => d2es of
    | cons (d2e1, d2es1) => let
        val d3e = d2exp_tr_dn (d2e, s2e_void)
      in
        cons (d3e, aux (d2e1, d2es1, s2e, s2e_void))
      end // end of [cons]
    | nil () => let
        val d3e = d2exp_tr_up (d2e)
      in
        s2e := d3e.d3exp_typ; cons (d3e, nil ())
      end // end of [nil]
  end // end of [aux]
  val s2e_void = s2exp_void_t0ype ()
in
  case+ d2es of
  | cons (d2e, d2es) => let
      var s2e: s2exp // uninitialized
      val d3es = aux (d2e, d2es, s2e, s2e_void)
    in
      d3exp_seq (loc0, s2e, d3es)
    end // end of [cons]
  | nil () => d3exp_empty (loc0, s2e_void)
end // end of [d2exp_seq_tr_up]

(* ****** ****** *)

fn d2exp_tmpid_tr_up
  (loc0: loc_t, d2e: d2exp, ts2ess: tmps2explstlst): d3exp = let
  fun aux (subs: List stasub_t): s2explstlst = case+ subs of
    | cons (sub, subs) => cons (stasub_codomain_get_whnf sub, aux subs)
    | nil () => nil ()
in
  case+ d2e.d2exp_node of
  | D2Ecst d2c => let
      val s2e_d2c = d2cst_typ_get (d2c)
      val s2vpss = d2cst_decarg_get (d2c)
      val (subs, s2e_tmp) = begin
        s2exp_template_instantiate (loc0, s2vpss, ts2ess, s2e_d2c)
      end
      val s2ess = aux subs
    in
      d3exp_tmpcst (loc0, s2e_tmp, d2c, s2ess)
    end
  | D2Evar d2v => let
      val s2e_d2v = d2var_typ_get_some (loc0, d2v)
      val s2vpss = d2var_decarg_get (d2v)
      val (subs, s2e_tmp) = begin
        s2exp_template_instantiate (loc0, s2vpss, ts2ess, s2e_d2v)
      end
      val s2ess = aux subs
    in
      d3exp_tmpvar (loc0, s2e_tmp, d2v, s2ess)
    end
  | _ => begin
      prerr loc0;
      prerr ": error(3)";
      $Deb.debug_prerrf (": %s: d2exp_tmpid_tr_up", @(THISFILENAME));
      prerr ": the dynamic expression is expected to be a constant or a variable.";
      prerr_newline ();
      $Err.abort {d3exp} ()
    end
end // end of [d2exp_tmpid_tr_up]

(* ****** ****** *)

fn d2exp_viewat_tr_up (loc0: loc_t, d2e0: d2exp): d3exp = let
  val l2v0 = l2val_make_d2exp d2e0
in
  case+ l2v0 of
  | L2VALptr (d2e_ptr, d2ls) => let
      val d3e_ptr = d2exp_tr_up d2e_ptr
      val () = d3exp_open_and_add d3e_ptr
      val s2e_ptr = d3e_ptr.d3exp_typ
      val d3ls_nt = d2lablst_tr_up d2ls
      val s2ls_nt = s2lab0lst_of_d3lab0lst d3ls_nt
    in
      case+ un_s2exp_ptr_addr_type s2e_ptr of
      | ~Some_vt s2e_addr => let
          val (s2e_at, s2ls, d2v_view, s2ls_view) =
            s2exp_addr_viewat_slablst_get (loc0, s2e_addr, s2ls_nt)
          val d3ls = d3lab1lst_of_d3lab0lst_s2lablst (d3ls_nt, s2ls)
        in
          d3exp_viewat_ptr (loc0, s2e_at, d3e_ptr, d3ls, d2v_view, s2ls_view)
        end
      | ~None_vt () => begin
          prerr d2e_ptr.d2exp_loc;
          prerr ": error(3)";
          prerr ": the dynamic expression is expected to be a pointer";
          prerr ", but it is given the type ["; prerr s2e_ptr; prerr "].";
          prerr_newline ();
(*
          prerr "d2e_ptr = "; prerr d2e_ptr; prerr_newline ();
*)
          $Err.abort {d3exp} ()
        end
      // end of [case]
    end
  | L2VALvar_mut (d2v, d2ls) => let
      val d3ls_nt = d2lablst_tr_up d2ls
      val s2ls_nt = s2lab0lst_of_d3lab0lst d3ls_nt
      val s2e_addr = d2var_addr_get_some (loc0, d2v)
      val @(s2e_at, s2ls, d2v_view, s2ls_view) =
        s2exp_addr_viewat_slablst_get (loc0, s2e_addr, s2ls_nt)
      val d3ls = d3lab1lst_of_d3lab0lst_s2lablst (d3ls_nt, s2ls)
    in
      d3exp_viewat_var (loc0, s2e_at, d2v, d3ls, d2v_view, s2ls_view)
    end
  | L2VALarrsub _ => begin
      prerr d2e0.d2exp_loc;
      prerr ": error(3)";
      prerr ": array subscription is not supported for view extraction.";
      prerr_newline ();
      $Err.abort {d3exp} ()
    end
  | L2VALvar_lin (d2v, _) => begin
      prerr d2e0.d2exp_loc;
      prerr ": error(3)";
      prerr ": the dynamic expression is expected to be a left-value";
      prerr ", but it is not as ["; prerr d2v; prerr "] is not mutable.";
      prerr_newline ();
      $Err.abort {d3exp} ()
    end 
  | L2VALnone _ => begin
      prerr d2e0.d2exp_loc;
      prerr ": error(3)";
      prerr ": the dynamic expression is expected to be a left-value";
      prerr ", but it is not.";
      prerr_newline ();
      $Err.abort {d3exp} ()
    end
end // end of [d2exp_viewat_tr_up]

(* ****** ****** *)

// the function is declared above
implement d2exp_viewat_assgn_tr_up (loc0, d2e_l, d2e_r) = let
  val l2v = l2val_make_d2exp d2e_l
in
  case+ l2v of
  | L2VALptr (d2e_ptr, d2ls) => let
      val d3e_ptr = d2exp_tr_up d2e_ptr
      val s2e_ptr = (d3exp_open_and_add d3e_ptr; d3e_ptr.d3exp_typ)
      val d3ls_nt = d2lablst_tr_up d2ls
      val s2ls_nt = s2lab0lst_of_d3lab0lst d3ls_nt
      val d3e_r = d2exp_tr_up d2e_r
      val s2e_r = (d3exp_open_and_add d3e_r; d3e_r.d3exp_typ)
    in
      case+ un_s2exp_ptr_addr_type s2e_ptr of
      | ~Some_vt s2e_addr => let
          val s2ls = begin
            s2exp_addr_viewat_slablst_set (loc0, s2e_addr, s2ls_nt, s2e_r)
          end
          val d3ls = d3lab1lst_of_d3lab0lst_s2lablst (d3ls_nt, s2ls)
        in
          d3exp_viewat_assgn_ptr (loc0, d3e_ptr, d3ls, d3e_r)
        end
      | ~None_vt () => begin
          prerr d2e_ptr.d2exp_loc;
          prerr ": error(3)";
          prerr ": the dynamic expression is expected to be a pointer";
          prerr ", but it is given the type ["; prerr s2e_ptr; prerr "].";
          prerr_newline ();
          $Err.abort {d3exp} ()
        end
    end // end of [L2VALptr]
  | L2VALvar_mut (d2v, d2ls) => let
      val d3ls_nt = d2lablst_tr_up d2ls
      val s2ls_nt = s2lab0lst_of_d3lab0lst d3ls_nt
      val d3e_r = d2exp_tr_up d2e_r
      val s2e_r = (d3exp_open_and_add d3e_r; d3e_r.d3exp_typ)
    in
      case+ d2ls of
      | cons _ => let
          val s2e_addr = d2var_addr_get_some (loc0, d2v)
          val s2ls = begin
            s2exp_addr_viewat_slablst_set (loc0, s2e_addr, s2ls_nt, s2e_r)
          end
          val d3ls = d3lab1lst_of_d3lab0lst_s2lablst (d3ls_nt, s2ls)
        in
          d3exp_viewat_assgn_var (loc0, d2v, d3ls, d3e_r)
        end
      | nil _ => let
          val d2v_view = d2var_view_get_some (loc0, d2v)
          val () = case+ d2var_typ_get (d2v_view) of
            | Some s2e_at => $SOL.s2exp_out_void_solve_at (loc0, s2e_at)
            | None () => ()
          val () = d2var_typ_set (d2v_view, Some s2e_r)
        in
          d3exp_viewat_assgn_var (loc0, d2v, nil (), d3e_r)
        end
      // end of [case]
    end // end of [L2VALvar_mul]
  | L2VALarrsub _ => begin
      prerr d2e_l.d2exp_loc;
      prerr ": error(3)";
      prerr ": array subscription is not supported for view assignment.";
      prerr_newline ();
      $Err.abort {d3exp} ()
    end // end of [L2VALarrsub]
  | L2VALvar_lin (d2v, _) => begin
      prerr d2e_l.d2exp_loc;
      prerr ": error(3)";
      prerr ": the dynamic expression is expected to be a left-value";
      prerr ", but it is not as ["; prerr d2v; prerr "] is not mutable.";
      prerr_newline ();
      $Err.abort {d3exp} ()
    end // end of [L2VALvar_lin]
  | L2VALnone _ => begin
      prerr d2e_l.d2exp_loc;
      prerr ": error(3)";
      prerr ": the dynamic expression is expected to be a left-value";
      prerr ", but it is not.";
      prerr_newline ();
      $Err.abort {d3exp} ()
    end // end of [L2VALnone]
  // end of [case]
end // end of [d2exp_view_assgn_tr_up]

(* ****** ****** *)

fun d2explst_elt_tr_dn (d2es: d2explst, s2e: s2exp): d3explst = 
  case+ d2es of
  | cons (d2e, d2es) => begin
      cons (d2exp_tr_dn (d2e, s2e), d2explst_elt_tr_dn (d2es, s2e))
    end
  | nil () => nil ()

(* ****** ****** *)

implement d2exp_tr_up (d2e0) = let
(*
val () = begin
  prerr "d2exp_tr_up: d2e0 = "; prerr d2e0; prerr_newline ()
end
*)
extern fun floatkind_eval
  (_: string): $Syn.floatkind = "ats_trans3_floatkind_eval"
extern fun intkind_eval
  (_: string): $Syn.intkind = "ats_trans3_intkind_eval"

val loc0 = d2e0.d2exp_loc
val d3e0 = (case+ d2e0.d2exp_node of
  | D2Eann_type (d2e, s2e) => let
      val d3e = d2exp_tr_dn (d2e, s2exp_whnf s2e)
    in
      d3exp_ann_type (loc0, d3e, s2e)
    end // end of [D2Eann_type]
  | D2Eapps (d2e_fun, d2as_arg) => begin
    case+ d2e_fun.d2exp_node of
    | D2Emac d2m => let
        val d2e0 = $Mac.macro_eval_app_short (loc0, d2m, d2as_arg)
      in
        d2exp_tr_up (d2e0)
      end
    | D2Esym d2s => d2exp_apps_sym_tr_up (loc0, d2s, d2as_arg)
    | _ => let
        val d3e_fun = d2exp_tr_up d2e_fun
        val () = d3exp_open_and_add d3e_fun
      in
        d2exp_apps_tr_up (d3e_fun, d2as_arg)
      end // end of [_]
    end // end of [D2Eapps]
  | D2Earrsize (os2e_elt, d2es_elt) => let
      val sz = $Lst.list_length d2es_elt
      val s2e_elt = (case+ os2e_elt of
        | Some s2e => s2e | None () => let
            val s2t = s2rt_t0ype in s2exp_Var_make_srt (loc0, s2t)
          end // end of [None]
      ) : s2exp // end of [val]
      val d3es_elt = d2explst_elt_tr_dn (d2es_elt, s2e_elt)
      val s2e_arrsz = begin
        s2exp_arraysize_viewt0ype_int_viewt0ype (s2e_elt, sz)
      end // end of [val]
    in
      d3exp_arrsize (loc0, s2e_arrsz, s2e_elt, d3es_elt)
    end // end of [D2Earrsize]
  | D2Earrsub (d2s_brackets, d2e_arr, loc_ind, d2ess_ind) => begin
      if d2exp_var_is_ptr d2e_arr then let
        val d2l = d2lab_ind (loc_ind, d2ess_ind)
      in
        d2exp_deref_tr_up (loc0, d2e_arr, '[d2l])
      end else begin case+ d2ess_ind of
        | cons (d2es_ind, nil ()) => let
            val d2a = D2EXPARGdyn (loc0, 0, cons (d2e_arr, d2es_ind))
          in
            d2exp_apps_sym_tr_up (loc0, d2s_brackets, '[d2a])
          end // end of [cons]
        | _ => begin
            prerr loc_ind;
            prerr ": error(3)";
            prerr ": the format for array subscripts ["; prerr d2ess_ind;
            prerr "] is not supported."; prerr_newline ();
            $Err.abort {d3exp} ()
          end // end of [_]
      end // end of [if]
    end // end of [D2Earrsub]
  | D2Eassgn (d2e_l, d2e_r) => d2exp_assgn_tr_up (loc0, d2e_l, d2e_r)
  | D2Ecaseof (casknd, res, n, d2es, c2ls) => let
      val s2e_cas = s2exp_Var_make_srt (loc0, s2rt_t0ype)
    in
      d2exp_caseof_tr_dn (loc0, casknd, res, n, d2es, c2ls, s2e_cas)
    end // end of [D2Ecaseof]
  | D2Echar c(*char*) => let
      val s2e = s2exp_char_char_t0ype c
    in
      d3exp_char (loc0, s2e, c)
    end // end of [D2Echar]
  | D2Econ (d2c, s2as, npf, d2es) => begin
      d2exp_con_tr_up (loc0, d2c, s2as, npf, d2es)
    end // end of [D2Econ]
  | D2Ecrypt (knd, d2e) => d2exp_crypt_tr_up (loc0, knd, d2e)
  | D2Ecst d2c => d2exp_cst_tr_up (loc0, d2c)
  | D2Ederef d2e => d2exp_deref_tr_up (loc0, d2e, nil ())
  | D2Edynload fil => d3exp_dynload (loc0, fil)
  | D2Eeffmask (effs, d2e) => let
      val (pf_effect | ()) = the_effect_env_push_effmask (effs)
      val d3e = d2exp_tr_up d2e
      val () = the_effect_env_pop (pf_effect | (*none*))
    in
      d3exp_effmask (loc0, effs, d3e)
    end // end of [D2Eeffmask]
  | D2Eempty () => d3exp_empty (loc0, s2exp_void_t0ype ())
  | D2Eextval (s2e, code) => d3exp_extval (loc0, s2e, code)
  | D2Efoldat (s2as, d2e_at) => d2exp_foldat_tr_up (loc0, s2as, d2e_at)
  | D2Efor (lpi2nv, d2e_init, d2e_test, d2e_post, d2e_body) => begin
      d2exp_loop_tr_up (
        loc0, lpi2nv, Some d2e_init, d2e_test, Some d2e_post, d2e_body
      ) // end of [d2exp_loop_tr_up]
    end // end of [D2Efor]
  | D2Efreeat (s2as, d2e_at) => d2exp_freeat_tr_up (loc0, s2as, d2e_at)
  | D2Eif (res, d2e_cond, d2e_then, od2e_else) => let
      val s2e_if: s2exp = case+ od2e_else of
        | Some _ => s2exp_Var_make_srt (loc0, s2rt_t0ype)
        | None () => s2exp_void_t0ype ()
    in
      d2exp_if_tr_dn (loc0, res, d2e_cond, d2e_then, od2e_else, s2e_if)
    end // end of [D2Eif]
  | D2Efloat (str) => let
      val s2e = s2exp_double_t0ype ()
    in
      d3exp_float (loc0, s2e, str)
    end // end of [D2Efloat]
  | D2Efloatsp (str) => let
      val s2e = case+ floatkind_eval (str) of
        | $Syn.FLOATKINDfloat () => s2exp_float_t0ype ()
        | $Syn.FLOATKINDdouble () => s2exp_double_t0ype ()
        | $Syn.FLOATKINDdouble_long () => s2exp_double_long_t0ype ()
        | $Syn.FLOATKINDnone () => begin
            prerr loc0;
            prerr "Internal Error: d2exp_tr: D2Efloatsp: FLOATKINDnone";
            prerr_newline ();
            $Err.abort {s2exp} ()
          end
    in
      d3exp_floatsp (loc0, s2e, str)
    end // end of [D2Efloatsp]
  | D2Eint (str, int) => let
      val s2e = s2exp_int_intinf_t0ype int
    in
      d3exp_int (loc0, s2e, str, int)
    end // end of [D2Eint]
  | D2Eintsp (str, int) => let
      val s2e = case+ intkind_eval (str) of
        | $Syn.INTKINDlint () => s2exp_lint_t0ype ()
        | $Syn.INTKINDuint () => s2exp_uint_intinf_t0ype (int)
        | $Syn.INTKINDulint () => s2exp_ulint_t0ype ()
        | _ => begin
            prerr loc0;
            prerr "Internal Error: d2exp_tr: D2Eintsp";
            prerr_newline ();
            $Err.abort {s2exp} ()
          end
    in
      d3exp_intsp (loc0, s2e, str, int)
    end // end of [D2Eintsp]
  | D2Elam_dyn (lin, npf, p2ts_arg, d2e_body) => let
(*
      val () = begin
        prerr "d2exp_tr_up: D2Elam_dyn: p2ts_arg = ";
        prerr p2ts_arg; prerr_newline ();
        prerr "d2exp_tr_up: D2Elam_dyn: d2e_body = ";
        prerr d2e_body; prerr_newline ();
      end
*)
      val () = trans3_env_push_sta ()
      var fc: funclo = $Syn.FUNCLOfun ()
      val d2e_body = d2exp_funclo_of_d2exp (d2e_body, fc)
      var s2fe: s2eff // uninitialized
      val d2e_body = d2exp_s2eff_of_d2exp (d2e_body, s2fe)
      val (pf_effect | ()) = the_effect_env_push_lam (s2fe)
      val (pf_d2varset | ()) = the_d2varset_env_push_lam (lin)
(*
      val () = begin
        prerr "d2exp_tr_up: D2Elam_dyn: d2varset = ";
        the_d2varset_env_prerr_ld2vs; prerr_newline ()
      end
*)
      val () = the_d2varset_env_add_p2atlst p2ts_arg
(*
      val () = begin
        prerr "d2exp_tr_up: D2Elam_dyn: d2varset = ";
        the_d2varset_env_prerr_ld2vs; prerr_newline ()
      end
*)
      val s2es_arg = p2atlst_typ_syn p2ts_arg

      // checking for pattern match exhaustiveness
      val p2tcss = p2atcstlst_complement (p2atcstlst_of_p2atlst p2ts_arg)
(*
      val () = begin
        prerr "d2exp_tr_up: D2Elam_dyn: p2tcss = "; prerr p2tcss; prerr_newline ()
      end
*)
      val cmplt = (
        case+ p2tcss of cons _ => 0(*incomplete*) | nil _ => 1
      ) : int
      val () = if cmplt = 0 then begin
        trans3_env_add_p2atcstlstlst_false (loc0, 1(*casknd*), p2tcss, s2es_arg)
      end

      val p3ts_arg = p2atlst_arg_tr_up (npf, p2ts_arg)
      val (pf_lamloop | ()) = the_lamloop_env_push_lam (p3ts_arg)
      val d3e_body = d2exp_tr_up d2e_body
      val () = the_d2varset_env_check loc0
      val () = if lin > 0 then the_d2varset_env_check_llam loc0
      val () = the_lamloop_env_pop (pf_lamloop | (*none*))
      val () = the_d2varset_env_pop_lam (pf_d2varset | (*none*))
      val () = the_effect_env_pop (pf_effect | (*none*))
      val () = trans3_env_pop_sta_and_add_none (loc0)

      val s2e_res = d3e_body.d3exp_typ
      val isprf = s2exp_is_proof s2e_res
      val s2t_fun = s2rt_prf_lin_fc (loc0, isprf, lin > 0, fc)
      val s2e_fun =
        s2exp_fun_srt (s2t_fun, fc, lin, s2fe, npf, s2es_arg, s2e_res)
(*
      val () = begin
        prerr "d2exp_tr_up: D2Elam: s2e_fun = "; prerr s2e_fun; prerr_newline ()
      end // end of [val]
*)
    in
      d3exp_lam_dyn (loc0, s2e_fun, lin, npf, p3ts_arg, d3e_body)
    end // end of [D2Elam_dyn]
  | D2Elam_met (r_d2vs, s2es_met, d2e_body) => let
      val () = metric_nat_check (loc0, s2es_met)
      val (pf_metric | ()) = metric_env_push (!r_d2vs, s2es_met)
      val d3e_body = d2exp_tr_up d2e_body
      val () = metric_env_pop (pf_metric | (*none*))
    in
      d3exp_lam_met (loc0, s2es_met, d3e_body)
    end // end of [D2Elam_met]
  | D2Elam_sta (s2vs, s2ps, d2e_body) => let
      val () = trans3_env_push_sta ()
      val () = trans3_env_add_svarlst s2vs
      val () = trans3_env_hypo_add_proplst (loc0, s2ps)
      val d3e_body = d2exp_tr_up d2e_body
      val () = trans3_env_pop_sta_and_add_none (loc0)
      val s2e0 = s2exp_uni (s2vs, s2ps, d3e_body.d3exp_typ)
    in
      d3exp_lam_sta (loc0, s2e0, s2vs, s2ps, d3e_body)
    end // end of [D2Elam_sta]
  | D2Elazy_delay (lin, d2e) => let // as if checking [llam () =<~ref> d2e]
      val () = trans3_env_push_sta ()
      val (pf_effect1 | ()) = the_effect_env_push_effmask ($Eff.effectlst_all)
      val (pf_effect2 | ()) = the_effect_env_push_delay ()
      val (pf_d2varset | ()) = the_d2varset_env_push_lam (1(*linear*))
      val (pf_lamloop | ()) = the_lamloop_env_push_lam (nil ())
      val d3e = d2exp_tr_up d2e
      val () = the_d2varset_env_check loc0
      val () = the_d2varset_env_check_llam loc0
      val () = the_lamloop_env_pop (pf_lamloop | (*none*))
      val () = the_d2varset_env_pop_lam (pf_d2varset | (*none*))
      val () = the_effect_env_pop (pf_effect2 | (*none*))
      val () = the_effect_env_pop (pf_effect1 | (*none*))
      val () = trans3_env_pop_sta_and_add_none (loc0)
      val s2e = d3e.d3exp_typ
      val lin = (
        if lin > 0 then 1 else (if s2exp_is_linear s2e then 1 else 0)
      ) : int
      val s2e_lazy = (
        if lin > 0then begin
          s2exp_lazy_viewt0ype_viewtype s2e
        end else begin
          s2exp_lazy_t0ype_type s2e
        end
      ) : s2exp
    in
      d3exp_lazy_delay (loc0, s2e_lazy, lin, d3e)
    end // end of [D2Elazy_delay]
  | D2Elet (d2cs, d2e) => let
      val (pf_effect | ()) = the_effect_env_push ()
      val (pf_s2cstlst | ()) = the_s2cstlst_env_push ()
      val (pf_d2varset | ()) = the_d2varset_env_push_let ()
      val d3cs = d2eclst_tr d2cs; val d3e = d2exp_tr_up d2e
      val () = the_d2varset_env_check loc0
      val () = the_d2varset_env_pop_let (pf_d2varset | (*none*))
      val () = the_s2cstlst_env_pop_and_unbind (pf_s2cstlst | (*none*))
      val () = the_effect_env_pop (pf_effect | (*none*))
    in
      d3exp_let (loc0, d3cs, d3e)
    end // end of [D2Elet]
  | D2Eloopexn i => begin
      d2exp_loopexn_tr_up (loc0, i) // 0/1: break/continue
    end // end of [D2Eloopexn]
  | D2Elst (lin, os2e_elt, d2es_elt) => let
      val s2e_elt = case+ os2e_elt of
        | Some s2e_elt => s2e_elt
        | None () => let
            val s2t = if lin > 0 then s2rt_viewt0ype else s2rt_t0ype
          in
            s2exp_Var_make_srt (loc0, s2t)
          end
      // end of [val]
      val n = $Lst.list_length d2es_elt
      val d3es_elt = d2explst_elt_tr_dn (d2es_elt, s2e_elt)
      val s2e_lst: s2exp =
        if lin > 0 then begin
          s2exp_list_viewt0ype_int_viewtype (s2e_elt, n)
        end else begin
          s2exp_list_t0ype_int_type (s2e_elt, n)
        end
    in
      d3exp_lst (loc0, s2e_lst, lin, s2e_elt, d3es_elt)
    end // end of [D2Elst]
  | D2Emac d2m => let
      val d2as = list_nil () // no arguments for [d2m]
      val d2e0 = $Mac.macro_eval_app_short (loc0, d2m, d2as)
    in
      d2exp_tr_up (d2e0)
    end // end of [D2Emac]
  | D2Emacsyn (knd, d2e) => let
      val d2e = case+ knd of
        | $Syn.MACSYNKINDcross () => $Mac.macro_eval_cross (d2e)
        | $Syn.MACSYNKINDdecode () => $Mac.macro_eval_decode (d2e) 
        | $Syn.MACSYNKINDencode () => begin
            prerr loc0; prerr ": error(macro)";
            prerr ": the macro syntax `(...) is incorrectly used at this location.";
            prerr_newline ();
            $Err.abort {d2exp} ()
          end
(*
      val () = begin
        prerr "d2exp_tr_up: D2Emacsyn: d2e = "; prerr d2e; prerr_newline ()
      end
*)
    in
      d2exp_tr_up d2e
    end // end of [D2Emacsyn]
  | D2Eptrof d2e =>  d2exp_ptrof_tr_up (loc0, d2e)
  | D2Eraise d2e_exn => let
      val s2e_exn = s2exp_exception_viewtype ()
      val d3e_exn = d2exp_tr_dn (d2e_exn, s2e_exn)
      val s2e_raise = s2exp_bottom_viewt0ype_uni ()
    in
      d3exp_raise (loc0, s2e_raise, d3e_exn)
    end // end of [D2Eraise]
  | D2Erec (recknd, npf, ld2es) => begin
      d2exp_rec_tr_up (loc0, recknd, npf, ld2es)
    end // end of [D2Erec]
  | D2Escaseof (res, s2e_val, sc2ls) => let
      val s2e_scase = s2exp_Var_make_srt (loc0, s2rt_prop)
    in
      d2exp_scaseof_tr_dn (loc0, res, s2e_val, sc2ls, s2e_scase)
    end // end of [D2Escaseof]
  | D2Esel (d2e, d2ls) => d2exp_sel_tr_up (loc0, d2e, d2ls)
  | D2Eseq d2es => d2exp_seq_tr_up (loc0, d2es)
  | D2Esif (r2es, s2p_cond, d2e_then, d2e_else) => let
      val s2e_sif = s2exp_Var_make_srt (loc0, s2rt_prop)
    in
      d2exp_sif_tr_dn (loc0, r2es, s2p_cond, d2e_then, d2e_else, s2e_sif)
    end // end of [D2Esif]
  | D2Estring (str, len) => let
      val s2e = s2exp_string_int_type (string0_length str)
    in
      d3exp_string (loc0, s2e, str, len)
    end // end of [D2Estring]
  | D2Etmpid (d2e, ts2ess) => begin
      d2exp_tmpid_tr_up (loc0, d2e, ts2ess)
    end // end of [D2Etmpid]
  | D2Etop () => begin
      prerr loc0;
      prerr ": error(3)";
      prerr ": the type of [?] cannot be synthesized.";
      prerr_newline ();
      $Err.abort {d3exp} ()
    end // end of [D2Etop]
  | D2Etrywith (r2es, d2e, c2ls) => let
(*
      // [r2es] is not in use; it is always [in2vresstate_nil]
      val r2es = i2nvresstate_update (r2es) // each var is replaced with its view
*)
      val (pf_d2varset | ()) = the_d2varset_env_push_try ()
      val d3e = d2exp_tr_up d2e
      val s2e = d3e.d3exp_typ
      val s2e_pat = s2exp_exception_viewtype ()
      var cmplt: int = 0
      val c3ls = c2laulst_tr_dn (
        loc0, cmplt, ~1(*knd*), r2es, c2ls, '[d3e], 1, '[s2e_pat], s2e
      ) // end of [c2laulst_tr_dn]
      val () = the_d2varset_env_pop_try (pf_d2varset | (*none*))
    in
      d3exp_trywith (loc0, d3e, c3ls)
    end // end of [D2Etrywith]
  | D2Evar d2v => d2exp_var_tr_up (loc0, d2v)
  | D2Eviewat (d2e) => d2exp_viewat_tr_up (loc0, d2e)
  | D2Ewhere (d2e, d2cs) => let
      val (pf_effect | ()) = the_effect_env_push ()
      val (pf_s2cstlst | ()) = the_s2cstlst_env_push ()
      val (pf_d2varset | ()) = the_d2varset_env_push_let ()
      val d3cs = d2eclst_tr d2cs; val d3e = d2exp_tr_up d2e
      val () = the_d2varset_env_check loc0
      val () = the_d2varset_env_pop_let (pf_d2varset | (*none*))
      val () = the_s2cstlst_env_pop_and_unbind (pf_s2cstlst | (*none*))
      val () = the_effect_env_pop (pf_effect | (*none*))
    in
      d3exp_where (loc0, d3e, d3cs)
    end // end of [D2Ewhere]
  | D2Ewhile (lpi2nv, d2e_test, d2e_body) => d2exp_loop_tr_up
      (loc0, lpi2nv, None(*init*), d2e_test, None(*post*), d2e_body)
    // end of [D2Ewhile]
  | _ => begin
      $Loc.prerr_location loc0;
      prerr ": d2exp_tr_up: not implemented yet: d2e0 = ";
      prerr_d2exp d2e0;
      prerr_newline ();
      $Err.abort {d3exp} ()
    end // end of [_]
) : d3exp // end of [val]
(*
val () = begin
  prerr "d2exp_tr_up: d3e0 = "; prerr d3e0; prerr_newline ()
end
val s2e0 = d3e0.d3exp_type
val () = begin
  prerr "d2exp_tr_up: s2e0 = "; prerr s2e0; prerr_newline ()
end
*)

in // in of [let]
 
d3e0 (* the return value *)

end // end of [d2exp_tr_up]

implement d2explst_tr_up d2es = begin case+ d2es of
  | cons (d2e, d2es) => cons (d2exp_tr_up d2e, d2explst_tr_up d2es)
  | nil () => nil ()
end // end of [d2explst_tr_up]

implement d2explstlst_tr_up d2ess = begin case+ d2ess of
  | cons (d2es, d2ess) => cons (d2explst_tr_up d2es, d2explstlst_tr_up d2ess)
  | nil () => nil ()
end // end of [d2explstlst_tr_up]

(* ****** ****** *)

implement d2exp_cst_tr_up (loc0, d2c) = let
  val s2e_d2c = d2cst_typ_get d2c
in
  case+ d2cst_decarg_get d2c of
  | nil () => d3exp_cst (loc0, d2c)
  | s2vpss (* as cons _ *) => let
      val (subs, s2e_tmp) = begin
        s2exp_template_instantiate (loc0, s2vpss, TMPS2EXPLSTLSTnil (), s2e_d2c)
      end
      val s2ess = aux subs where {
        fun aux (subs: List stasub_t): s2explstlst = case+ subs of
          | cons (sub, subs) => cons (stasub_codomain_get_whnf sub, aux subs)
          | nil () => nil ()
      } // end of [where]
    in
      d3exp_tmpcst (loc0, s2e_tmp, d2c, s2ess)
    end
end // end of [d2exp_cst_tr_up]

(* ****** ****** *)

fn d2exp_var_mut_tr_up (loc0: loc_t, d2v: d2var_t): d3exp = let
(*
  val () = begin
    prerr "d2exp_var_mut_tr_up: d2v = "; prerr d2v; prerr_newline ()
  end
  val () = begin
    prerr "d2exp_var_mut_tr_up: d2varset = ";
    the_d2varset_env_prerr_ld2vs (); prerr_newline ()
  end
*)
  val s2e_addr = d2var_addr_get_some (loc0, d2v)
  val (s2e, _(*nil*)) = s2exp_addr_slablst_deref (loc0, s2e_addr, nil ())
in
  d3exp_var (loc0, s2e, d2v)
end // end of [d2exp_var_mut_tr_up]

fn d2exp_var_nonmut_tr_up (loc0: loc_t, d2v: d2var_t): d3exp = let
  val lin_d2v = d2var_lin_get (d2v)
  val s2e_d2v = d2var_typ_get_some (loc0, d2v)
(*
  val () = begin
    prerr "d2exp_var_nonmut_tr_up: d2v = "; prerr d2v; prerr_newline ()
  end
  val () = begin
    prerr "d2exp_var_nonmut_tr_up: lin_d2v = "; prerr lin_d2v; prerr_newline ()
  end
  val () = begin
    prerr "d2exp_var_nonmut_tr_up: d2varset = ";
    the_d2varset_env_prerr_ld2vs (); prerr_newline ()
  end
*)
  val () = begin
    if lin_d2v >= 0 then let
      val is_llam_local = the_d2varset_env_d2var_is_llam_local d2v
    in
      if is_llam_local then begin
        d2var_lin_set (d2v, 1+lin_d2v); d2var_typ_set (d2v, None ())
      end else begin
        prerr loc0;
        prerr ": error(3)";
        prerr ": the linear dynamic variable [";
        prerr d2v;
        prerr "] is expected to be local but it is not.";
        prerr_newline ();
        $Err.abort {void} ()
      end // end of [begin]
    end // end of [let]
  end // end of [begin]
in
  case+ d2var_decarg_get d2v of
  | nil () => d3exp_var (loc0, s2e_d2v, d2v)
  | s2vpss (* as cons _ *) => let
      val (subs, s2e_tmp) = begin
        s2exp_template_instantiate (loc0, s2vpss, TMPS2EXPLSTLSTnil (), s2e_d2v)
      end // end of [val]
      val s2ess = aux subs where {
        fun aux (subs: List stasub_t): s2explstlst = case+ subs of
          | cons (sub, subs) => cons (stasub_codomain_get_whnf sub, aux subs)
          | nil () => nil ()
      } // end of [where]
    in
      d3exp_tmpvar (loc0, s2e_tmp, d2v, s2ess)
    end
end // end of [d2exp_var_nonmut_tr_up]

implement d2exp_var_tr_up (loc0, d2v) = begin case+ d2v of
  | _ when d2var_is_mutable d2v => d2exp_var_mut_tr_up (loc0, d2v)
  | _ => d2exp_var_nonmut_tr_up (loc0, d2v)
end // end of [d2exp_var_tr_up]

(* ****** ****** *)

(* end of [ats_trans3_exp_up.dats] *)
