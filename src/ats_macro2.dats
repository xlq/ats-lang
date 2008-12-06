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

(* Mainly for handling macro expansion during type-checking *)

(* ****** ****** *)

%{^

#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
#include "ats_intinf.cats"  /* only needed for [ATS/Geizella] */

%}

(* ****** ****** *)

staload Err = "ats_error.sats"
staload IntInf = "ats_intinf.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"
staload Stamp = "ats_stamp.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

staload "ats_macro2.sats"

(* ****** ****** *)

overload = with $Sym.eq_symbol_symbol
overload prerr with $Loc.prerr_location

(* ****** ****** *)

datatype v2alue =
  | V2ALbool of bool
  | V2ALchar of char
  | V2ALcode of d2exp
  | V2ALfloat of string
  | V2ALint of intinf_t
  | V2ALlst of v2aluelst
  | V2ALstring of (string, int(*length*))
  | V2ALunit

where v2aluelst = List v2alue

viewtypedef v2alueopt_vt = Option_vt v2alue

val v2alue_bool_true = V2ALbool (true)
val v2alue_bool_false = V2ALbool (false)

fun fprint_v2alue {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, v2al: v2alue)
  : void = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ v2al of
  | V2ALbool b => begin
      strpr "V2ALbool("; fprint1_bool (pf | out, b); strpr ")"
    end
  | V2ALchar (c) => begin
      strpr "V2ALchar("; fprint1_char (pf | out, c); strpr ")"
    end
  | V2ALcode (d2e) => begin
      strpr "V2ALcode("; fprint_d2exp (pf | out, d2e); strpr ")"
    end
  | V2ALfloat f(*string*) => begin
      strpr "V2ALfloat("; fprint1_string (pf | out, f); strpr ")"
    end
  | V2ALint (i) => begin
      strpr "V2ALint(";
      $IntInf.fprint_intinf (pf | out, i);
      strpr ")"
    end
  | V2ALlst (vs) => begin
      fprint1_string (pf | out, "V2ALlst(...)")
    end
  | V2ALstring (str, len) => begin
      fprintf1_exn (pf | out, "V2ALstring(\"%s\", %i)", @(str, len))
    end
  | V2ALunit () => begin
      fprint1_string (pf | out, "V2ALunit()")
    end
end // end of [fprint_v2alue]

fn print_v2alue (v2al: v2alue): void = print_mac (fprint_v2alue, v2al)
fn prerr_v2alue (v2al: v2alue): void = prerr_mac (fprint_v2alue, v2al)

overload print with print_v2alue
overload prerr with prerr_v2alue

(* ****** ****** *)

fn lift_val_exp
  (loc0: loc_t, v2al: v2alue): d2exp = begin
  case+ v2al of
  | V2ALchar c => d2exp_char (loc0, c)
  | V2ALint int => begin
      d2exp_int (loc0, $IntInf.tostring_intinf int, int)
    end
  | V2ALfloat f(*string*) => d2exp_float (loc0, f)
  | V2ALstring (str, len) => d2exp_string (loc0, str, len)
  | V2ALunit () => d2exp_empty (loc0)
  | _ => begin
      prerr loc0; prerr ": error(macro)";
      prerr ": a value representing code (abstract syntax tree) cannot be lifted.";
      prerr_newline ();
      $Err.abort {d2exp} ()
    end
end // end of [lift_val_exp]

(* ****** ****** *)

dataviewtype alphaenv = 
  | ALPHAENVcons of (stamp_t, d2var_t, alphaenv)
  | ALPHAENVmark of alphaenv
  | ALPHAENVnil

fun alphaenv_free (env: alphaenv): void = begin
  case+ env of
  | ~ALPHAENVcons (_, _, env) => alphaenv_free env
  | ~ALPHAENVmark env => alphaenv_free env
  | ~ALPHAENVnil () => ()
end // end of [alphaenv_free]

fn alphaenv_add
  (env: alphaenv, d2v: d2var_t, d2v_new: d2var_t): alphaenv =
  ALPHAENVcons (d2var_stamp_get d2v, d2v_new, env)

fn alphaenv_find
  (env: !alphaenv, d2v0: d2var_t): Option_vt (d2var_t) = let
  fun aux (env: !alphaenv, stamp0: stamp_t): Option_vt (d2var_t) =
  case+ env of
  | ALPHAENVcons (stamp, d2v, !env_nxt) => let
      val ans = (
        if $Stamp.eq_stamp_stamp (stamp, stamp0) then Some_vt d2v
        else aux (!env_nxt, stamp0)
      ) : Option_vt d2var_t // end of [if]
    in
      fold@ env; ans
    end
  | ALPHAENVmark (!env_nxt) => let
      val ans = aux (!env_nxt, stamp0)
    in
      fold@ env; ans
    end
  | ALPHAENVnil () => (fold@ env; None_vt ())
in
  aux (env, d2var_stamp_get d2v0)
end // end of [alphaenv_find]

fn alphaenv_insert
  (env: &alphaenv, d2v: d2var_t, d2v_new: d2var_t): void =
  (env := ALPHAENVcons (d2var_stamp_get d2v, d2v_new, env))

fun alphaenv_pop (env: &alphaenv): void = let
  fun aux (env: alphaenv): alphaenv =
    case+ env of
    | ~ALPHAENVcons (_, _, env) => aux env
    | ~ALPHAENVmark env => env
    | ~ALPHAENVnil () => ALPHAENVnil ()
in
  env := aux (env)
end

fn alphaenv_push (env: &alphaenv): void = (env := ALPHAENVmark env)

(* ****** ****** *)

extern fun d2var_copy (loc: loc_t, d2v: d2var_t): d2var_t
implement d2var_copy (loc, d2v) = d2v

// eval0: evaluation at level 0
// eval1: evaluation at level 1

(* ****** ****** *)

extern fun eval1_p2at
  (loc0: loc_t, env: &alphaenv, p2t0: p2at): p2at

extern fun eval1_p2atlst {n:nat}
  (loc0: loc_t, env: &alphaenv, p2ts: p2atlst n): p2atlst n

extern fun eval1_labp2atlst
  (loc0: loc_t, env: &alphaenv, lp2ts: labp2atlst): labp2atlst

implement eval1_p2at (loc0, env, p2t0) = begin
  case+ p2t0.p2at_node of
  | P2Tann (p2t, s2e) => let
      val p2t = eval1_p2at (loc0, env, p2t)
    in
      p2at_ann (loc0, p2t, s2e)
    end
  | P2Tas (refknd, d2v, p2t) => let
      val d2v_new = d2var_copy (loc0, d2v)
      val () = alphaenv_insert (env, d2v, d2v_new)
      val p2t = eval1_p2at (loc0, env, p2t)
    in
      p2at_as (loc0, refknd, d2v_new, p2t)
    end
  | P2Tcon (freeknd, d2c, s2qs, s2e, npf, p2ts) => let
      val p2ts = eval1_p2atlst (loc0, env, p2ts)
    in
      p2at_con (loc0, freeknd, d2c, s2qs, s2e, npf, p2ts)
    end
  | P2Texist (s2vs, p2t) => let
      val p2t = eval1_p2at (loc0, env, p2t)
    in
      p2at_exist (loc0, s2vs, p2t)
    end
  | P2Tlist (npf, p2ts) => let
      val p2ts = eval1_p2atlst (loc0, env, p2ts)
    in
      p2at_list (loc0, npf, p2ts)
    end
  | P2Tlst (p2ts) => let
      val p2ts = eval1_p2atlst (loc0, env, p2ts)
    in
      p2at_lst (loc0, p2ts)
    end
  | P2Trec (recknd, npf, lp2ts) => let
      val lp2ts = eval1_labp2atlst (loc0, env, lp2ts)
    in
      p2at_rec (loc0, recknd, npf, lp2ts)
    end
  | P2Tvar (refknd, d2v) => let
      val d2v_new = d2var_copy (loc0, d2v)
      val () = alphaenv_insert (env, d2v, d2v_new)
    in
      p2at_var (loc0, refknd, d2v_new)
    end
  | _ => p2t0
end // end of [eval1_p2at]

implement eval1_p2atlst (loc0, env, p2ts) = let
  fun aux {n:nat} (
      loc0: loc_t
    , env: &alphaenv
    , p2ts: p2atlst n
    , res: &p2atlst? >> p2atlst n
    ) : void = begin
    case+ p2ts of
    | list_cons (p2t, p2ts) => let
        val p2t = eval1_p2at (loc0, env, p2t)
        val () = (res := list_cons {p2at} {0} (p2t, ?))
        val+ list_cons (_, !res_nxt) = res
      in
        aux (loc0, env, p2ts, !res_nxt); fold@ res
      end
    | list_nil () => (res := list_nil ())
  end // end of [aux]
  var res: p2atlst? // uninitialized
in
  aux (loc0, env, p2ts, res); res
end

implement eval1_labp2atlst (loc0, env, lp2ts) = let
  fun aux (
      loc0: loc_t
    , env: &alphaenv
    , lp2ts: labp2atlst
    , res: &labp2atlst? >> labp2atlst
    ) : void = begin
    case+ lp2ts of
    | LABP2ATLSTcons (l, p2t, lp2ts) => let
        val p2t = eval1_p2at (loc0, env, p2t)
        val () = (res := LABP2ATLSTcons (l, p2t, ?))
        val+ LABP2ATLSTcons (_, _, !res_nxt) = res
      in
        aux (loc0, env, lp2ts, !res_nxt); fold@ res
      end
    | LABP2ATLSTdot () => (res := LABP2ATLSTdot ())
    | LABP2ATLSTnil () => (res := LABP2ATLSTnil ())
  end // end of [aux]
  var res: labp2atlst? // uninitialized
in
  aux (loc0, env, lp2ts, res); res
end

(* ****** ****** *)

dataviewtype eval0ctx =
  | EVAL0CTXcons of (stamp_t, v2alue, eval0ctx)
  | EVAL0CTXnil

fun eval0ctx_free (ctx: eval0ctx): void = begin
  case+ ctx of
  | ~EVAL0CTXcons (_, _, ctx) => eval0ctx_free ctx
  | ~EVAL0CTXnil () => ()
end // end of [eval0ctx_free]

fn eval0ctx_add
  (ctx: eval0ctx, d2v: d2var_t, v2al: v2alue): eval0ctx =
  EVAL0CTXcons (d2var_stamp_get d2v, v2al, ctx)

(* ****** ****** *)

fun fprint_eval0ctx {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, ctx: !eval0ctx)
  : void = begin case+ ctx of
  | EVAL0CTXcons (stamp, v2al, !ctx_nxt) => begin
      $Stamp.fprint_stamp (pf | out, stamp);
      fprint1_string (pf | out, " -> ");
      fprint_v2alue (pf | out, v2al);
      fprint_newline (pf | out);
      fprint_eval0ctx (pf | out, !ctx_nxt);
      fold@ ctx
    end // end of [EVAL0CTXcons]
  | EVAL0CTXnil () => (fold@ ctx)
end // end of [fprint_eval0ctx]

fn print_eval0ctx (ctx: !eval0ctx): void = print_mac (fprint_eval0ctx, ctx)
fn prerr_eval0ctx (ctx: !eval0ctx): void = prerr_mac (fprint_eval0ctx, ctx)

overload print with print_eval0ctx
overload prerr with prerr_eval0ctx

(* ****** ****** *)

extern fun eval0_exp
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, d2e: d2exp): v2alue

extern fun eval0_labexplst
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, ld2e: labd2explst): v2aluelst

(* ****** ****** *)

extern fun eval0_exp_app_mac_long {narg:nat} (
    loc0: loc_t
  , d2m: d2mac_t narg
  , ctx: !eval0ctx
  , env: &alphaenv
  , d2as: d2exparglst
  ) : v2alue

extern fun eval0_exp_app_mac_short {narg:nat} (
    loc0: loc_t
  , d2m: d2mac_t narg
  , ctx: !eval0ctx
  , env: &alphaenv
  , d2as: d2exparglst
  ) : d2exp

(* ****** ****** *)

// not qualified dynamic symbol
fn d2sym_is_nonqua (d2s: d2sym): bool = let
  val q = d2s.d2sym_qua
in
  case+ q.d0ynq_node of $Syn.D0YNQnone () => true | _ => false
end // end of [d2sym_is_nonqua]

(* ****** ****** *)

extern fun eval0_exp_app_sym (
    loc0: loc_t
  , sym: sym_t
  , ctx: !eval0ctx
  , env: &alphaenv
  , d2as: d2exparglst
  ) : v2alue

(* ****** ****** *)

fn eval0_exp_app_compare_sgn
  (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): Sgn = let
  fn err (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): Sgn = begin
    prerr loc0; prerr ": error(macro)";
    prerr ": values that do not support comparison are compared.";
    prerr_newline ();
    $Err.abort {Sgn} ()
  end
in
  case+ v2al1 of
  | V2ALint i1 => begin case+ v2al2 of
    | V2ALint i2 => $IntInf.compare_intinf_intinf (i1, i2)
    | _ => err (loc0, v2al1, v2al2)
    end
  | _ => err (loc0, v2al1, v2al2)
end // end of [eval0_exp_app_compare]

fn eval0_exp_app_gt
  (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): v2alue = let
  val sgn = eval0_exp_app_compare_sgn (loc0, v2al1, v2al2)
in
  if sgn > 0 then v2alue_bool_true else v2alue_bool_false
end

fn eval0_exp_app_gte
  (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): v2alue = let
  val sgn = eval0_exp_app_compare_sgn (loc0, v2al1, v2al2)
in
  if sgn >= 0 then v2alue_bool_true else v2alue_bool_false
end

fn eval0_exp_app_lt
  (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): v2alue = let
  val sgn = eval0_exp_app_compare_sgn (loc0, v2al1, v2al2)
in
  if sgn < 0 then v2alue_bool_true else v2alue_bool_false
end

fn eval0_exp_app_lte
  (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): v2alue = let
  val sgn = eval0_exp_app_compare_sgn (loc0, v2al1, v2al2)
in
  if sgn <= 0 then v2alue_bool_true else v2alue_bool_false
end

fn eval0_exp_app_eq
  (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): v2alue = let
  val sgn = eval0_exp_app_compare_sgn (loc0, v2al1, v2al2)
in
  if sgn = 0 then v2alue_bool_true else v2alue_bool_false
end

fn eval0_exp_app_neq
  (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): v2alue = let
  val sgn = eval0_exp_app_compare_sgn (loc0, v2al1, v2al2)
in
  if sgn <> 0 then v2alue_bool_true else v2alue_bool_false
end

(* ****** ****** *)

fn eval0_exp_app_neg
  (loc0: loc_t, v2al: v2alue): v2alue = let
  fn err (loc0: loc_t, v2al: v2alue): v2alue = begin
    prerr loc0; prerr ": error(macro)";
    prerr ": negation is performed on a value that does not support it.";
    prerr_newline ();
    $Err.abort {v2alue} ()
  end
in
  case+ v2al of
  | V2ALbool b => if b then v2alue_bool_false else v2alue_bool_true
  | V2ALint i => V2ALint ($IntInf.neg_intinf i)
  | _ => err (loc0, v2al)
end // end of [eval0_exp_app_add]

fn eval0_exp_app_add
  (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): v2alue = let
  fn err (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): v2alue = begin
    prerr loc0; prerr ": error(macro)";
    prerr ": addition is performed on values that do not support it.";
    prerr_newline ();
    $Err.abort {v2alue} ()
  end
in
  case+ v2al1 of
  | V2ALint i1 => begin case+ v2al2 of
    | V2ALint i2 => V2ALint ($IntInf.add_intinf_intinf (i1, i2))
    | _ => err (loc0, v2al1, v2al2)
    end
  | _ => err (loc0, v2al1, v2al2)
end // end of [eval0_exp_app_add]

fn eval0_exp_app_sub
  (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): v2alue = let
  fn err (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): v2alue = begin
    prerr loc0; prerr ": error(macro)";
    prerr ": subtraction is performed on values that do not support it.";
    prerr_newline ();
    $Err.abort {v2alue} ()
  end
in
  case+ v2al1 of
  | V2ALint i1 => begin case+ v2al2 of
    | V2ALint i2 => V2ALint ($IntInf.sub_intinf_intinf (i1, i2))
    | _ => err (loc0, v2al1, v2al2)
    end
  | _ => err (loc0, v2al1, v2al2)
end // end of [eval0_exp_app_sub]

fn eval0_exp_app_mul
  (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): v2alue = let
  fn err (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): v2alue = begin
    prerr loc0; prerr ": error(macro)";
    prerr ": multiplication is performed on values that do not support it.";
    prerr_newline ();
    $Err.abort {v2alue} ()
  end
in
  case+ v2al1 of
  | V2ALint i1 => begin case+ v2al2 of
    | V2ALint i2 => V2ALint ($IntInf.mul_intinf_intinf (i1, i2))
    | _ => err (loc0, v2al1, v2al2)
    end
  | _ => err (loc0, v2al1, v2al2)
end // end of [eval0_exp_app_mul]

(*
fn eval0_exp_app_div
  (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): v2alue = let
  fn err (loc0: loc_t, v2al1: v2alue, v2al2: v2alue): v2alue = begin
    prerr loc0; prerr ": error(macro)";
    prerr ": division is performed on values that do not support it.";
    prerr_newline ();
    $Err.abort {v2alue} ()
  end
in
  case+ v2al1 of
  | V2ALint i1 => begin case+ v2al2 of
    | V2ALint i2 => V2ALint (i1 / i2) | _ => err (loc0, v2al1, v2al2)
    end
  | _ => err (loc0, v2al1, v2al2)
end // end of [eval0_exp_app_div]
*)

(* ****** ****** *)

fn eval0_exp_app_is_nil (loc0: loc_t, v2al: v2alue): v2alue = let
  fn err (loc0: loc_t, v2al: v2alue): v2alue = begin
    prerr loc0; prerr ": error(macro)";
    prerr ": [is_nil] is performed on a value that do not support it.";
    prerr_newline ();
    $Err.abort {v2alue} ()
  end
in
  case+ v2al of
  | V2ALlst (vs) => begin case+ vs of
    | list_cons _ => v2alue_bool_false | list_nil () => v2alue_bool_true
    end
  | _ => err (loc0, v2al)
end // end of [eval0_exp_app_is_nil]

fn eval0_exp_app_is_cons (loc0: loc_t, v2al: v2alue): v2alue = let
  fn err (loc0: loc_t, v2al: v2alue): v2alue = begin
    prerr loc0; prerr ": error(macro)";
    prerr ": [is_cons] is performed on a value that do not support it.";
    prerr_newline ();
    $Err.abort {v2alue} ()
  end
in
  case+ v2al of
  | V2ALlst (vs) => begin case+ vs of
    | list_cons _ => v2alue_bool_false | list_nil () => v2alue_bool_true
    end
  | _ => err (loc0, v2al)
end // end of [eval0_exp_app_is_cons]

(* ****** ****** *)

fn eval0_exp_app_tup_head (loc0: loc_t, v2al: v2alue): v2alue = let
(*
  val () = begin
    prerr "eval0_exp_app_tup_head: v2al = "; prerr v2al; prerr_newline ()
  end
*)
  fn err (loc0: loc_t, v2al: v2alue): v2alue = begin
    prerr loc0; prerr ": error(macro)";
    prerr ": [tup_head] is performed on a value that do not support it.";
    prerr_newline ();
    $Err.abort {v2alue} ()
  end
  val ret = case+ v2al of
    | V2ALlst (vs) => begin case+ vs of
      | list_cons (v, _) => v | list_nil _ => err (loc0, v2al)
      end
    | _ => err (loc0, v2al)
(*
  val () = begin
    prerr "eval0_exp_app_tup_head: ret = "; prerr ret; prerr_newline ()
  end
*)
in
  ret // the return value
end // end of [eval0_exp_app_tup_head]

fn eval0_exp_app_tup_tail (loc0: loc_t, v2al: v2alue): v2alue = let
(*
  val () = begin
    prerr "eval0_exp_app_tup_tail: v2al = "; prerr v2al; prerr_newline ()
  end
*)
  fn err (loc0: loc_t, v2al: v2alue): v2alue = begin
    prerr loc0; prerr ": error(macro)";
    prerr ": [tup_tail] is performed on a value that do not support it.";
    prerr_newline ();
    $Err.abort {v2alue} ()
  end
  val ret = case+ v2al of
    | V2ALlst (vs) => begin case+ vs of
      | list_cons (_, vs) => V2ALlst (vs) | list_nil _ => err (loc0, v2al)
      end
    | _ => err (loc0, v2al)
(*
  val () = begin
    prerr "eval0_exp_app_tup_tail: ret = "; prerr ret; prerr_newline ()
  end
*)
in
  ret // the return value
end // end of [eval0_exp_app_tup_tail]

(* ****** ****** *)

fn eval0_exp_app_eval
  (loc0: loc_t, v2al: v2alue): v2alue = let
  fn err (loc0: loc_t, v2al: v2alue): v2alue = begin
    prerr loc0; prerr ": error(macro)";
    prerr ": evaluation is performed on a value not representing code.";
    prerr_newline ();
    $Err.abort {v2alue} ()
  end
in
  case+ v2al of
  | V2ALcode d2e => let
      var ctx = EVAL0CTXnil ()
      var env = ALPHAENVnil ()
      val v2al_res = eval0_exp (loc0, ctx, env, d2e)
      val () = alphaenv_free env
      val () = eval0ctx_free ctx
    in
      v2al_res
    end
  | _ => err (loc0, v2al)
end // end of [eval0_exp_app_eval]

fn eval0_exp_app_lift
  (loc0: loc_t, v2al: v2alue): v2alue = begin
  V2ALcode (lift_val_exp (loc0, v2al))
end // end of [eval0_exp_app_lift]

(* ****** ****** *)

extern fun eval1_d2exp
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, d2e0: d2exp): d2exp

extern fun eval1_d2explst {n:nat}
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, d2es: d2explst n): d2explst n

extern fun eval1_d2explstlst
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, d2ess: d2explstlst): d2explstlst

extern fun eval1_labd2explst
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, ld2es: labd2explst): labd2explst

extern fun eval1_d2ec
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, d2c0: d2ec): d2ec

extern fun eval1_d2eclst
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, d2cs: d2eclst): d2eclst

(* ****** ****** *)

fun eval0_var (loc0: loc_t, ctx: !eval0ctx, d2v: d2var_t): v2alue = let
  fn err (loc0: loc_t, d2v: d2var_t): v2alue = begin
     prerr loc0; prerr ": error(macro)";
     prerr ": the variable ["; prerr d2v; prerr "] is unbound.";
     prerr_newline ();
     $Err.abort {v2alue} ()
  end
  fun auxfind
    (ctx: !eval0ctx, stamp0: stamp_t):<cloptr1> v2alue =
    case+ ctx of
    | EVAL0CTXcons (stamp, v2al, !ctx_nxt) => let
        val ans: v2alue = begin
          if $Stamp.eq_stamp_stamp (stamp, stamp0) then v2al
          else auxfind (!ctx_nxt, stamp0)
        end
      in
        fold@ ctx; ans
      end
    | EVAL0CTXnil () => (fold@ ctx; err (loc0, d2v))
in
  auxfind (ctx, d2var_stamp_get d2v)
end

(* ****** ****** *)

implement eval0_exp (loc0, ctx, env, d2e0) = begin
  case+ d2e0.d2exp_node of
  | D2Eapps (d2e, d2as) => begin
    case+ d2e.d2exp_node of
    | D2Emac d2m => begin
        // expanding a macro in long form
        eval0_exp_app_mac_long (loc0, d2m, ctx, env, d2as)
      end
    | D2Esym d2s when d2sym_is_nonqua d2s => begin
        // evaluating a predefined function (e.g., +, -, etc.)
        eval0_exp_app_sym (loc0, d2s.d2sym_sym, ctx, env, d2as)
      end
    | _ => begin
        prerr loc0;
        prerr ": error(macro)";
        prerr ": the dynamic expression (";
        prerr d2e.d2exp_loc;
        prerr ") should be a macro but it is not.";
        prerr_newline ();
        $Err.abort {v2alue} ()
      end
    end // end of [D2Eapps]
  | D2Echar chr => V2ALchar chr
  | D2Efloat f(*string*) => V2ALfloat f
  | D2Eif (_(*inv*), d2e_cond, d2e_then, od2e_else) => let
      val v2al_cond = eval0_exp (loc0, ctx, env, d2e_cond)
    in
      case+ v2al_cond of
      | V2ALbool b => begin
          if b then eval0_exp (loc0, ctx, env, d2e_then)
          else begin case+ od2e_else of
          | Some d2e_else => eval0_exp (loc0, ctx, env, d2e_else)
          | None () => V2ALunit ()
          end // end of [if]
        end
      | _ => begin
          prerr loc0; prerr ": error(macro)";
          prerr ": the expansion of the dynamic expression (";
          prerr d2e_cond.d2exp_loc;
          prerr ") should return a boolean value but it did not.";
          prerr_newline ();
          $Err.abort {v2alue} ()
        end
    end // end of [D2Eif]
  | D2Eint (str, int) => V2ALint int
  | D2Emac d2m => let
      val d2as = list_nil () // no arguments for [d2m]
    in
      eval0_exp_app_mac_long (loc0, d2m, ctx, env, d2as)
    end
  | D2Emacsyn (knd, d2e) => begin case+ knd of
    | $Syn.MACSYNKINDcross () => let
        val v2al = eval0_exp (loc0, ctx, env, d2e)
        val v2al_res = eval0_exp_app_eval (loc0, v2al)
      in
        V2ALcode (lift_val_exp (loc0, v2al_res))
      end
    | $Syn.MACSYNKINDdecode () => let
        val v2al = eval0_exp (loc0, ctx, env, d2e)
      in
        eval0_exp_app_eval (loc0, v2al)
      end
    | $Syn.MACSYNKINDencode () => let
        val d2e = eval1_d2exp (loc0, ctx, env, d2e)
      in
        V2ALcode (d2e)
      end
(*
    | _ => begin
        $Loc.prerr_location loc0;
        prerr ": error(macro)";
        prerr ": invalid use of macro syntax: ";
        prerr d2e0; prerr_newline ();
        $Err.abort {v2alue} ()
      end
*)
    end // end of [D2Emacsyn]
  | D2Estring (str, len) => V2ALstring (str, len)
  | D2Erec (_(*recknd*), _(*npf*), ld2es) => let
      val v2ls = eval0_labexplst (loc0, ctx, env, ld2es)
    in
      V2ALlst (v2ls)
    end // end of [D2Erec]
  | D2Evar d2v => eval0_var (loc0, ctx, d2v)
  | _ => begin
      prerr loc0;
      prerr ": error(macro)";
      prerr ": unsupported form for macro expansion: ";
      prerr d2e0; prerr_newline ();
      $Err.abort {v2alue} ()
    end // end of [_]
end // end of [eval0_exp]

implement eval0_labexplst
  (loc0, ctx, env, ld2es) = begin case+ ld2es of
  | LABD2EXPLSTcons (_(*lab*), d2e, ld2es) => let
      val v2l = eval0_exp (loc0, ctx, env, d2e)
    in
      list_cons (v2l, eval0_labexplst (loc0, ctx, env, ld2es))
    end // end of [LABD2EXPLSTcons]
  | LABD2EXPLSTnil () => list_nil ()
end // end of [eval0_labexplst]

(* ****** ****** *)

fn d2exparg_dyn_get {n:nat} (
    loc0: loc_t
  , sym: sym_t
  , d2a: d2exparg
  , n: int n
  ) : d2explst n = begin case+ d2a of
  | D2EXPARGdyn (_(*loc*), _(*npf*), d2es) => let
      stavar nd2es: int
      val nd2es: int(nd2es) = $Lst.list_length d2es
      val () = ( // arity checking
        if nd2es <> n then begin
          prerr loc0; prerr ": error(macro)";
          prerr ": the dynamic symbol [";
          $Sym.prerr_symbol sym;
          if nd2es > 2 then prerr "] expects two arguments but is given more.";
          if nd2es < 2 then prerr "] expects two arguments but is given less.";
          prerr_newline ();
          $Err.abort {void} ();
          assert (nd2es = n) // deadcode
        end else begin
          () // [nd2es = n] holds!
        end
      ) : [nd2es==n] void // end of [if]
    in
      d2es
    end // end of [D2EXPARGdyn]
  | D2EXPARGsta _ => begin
      prerr loc0;
      prerr ": error(macro)";
      prerr ": the dynamic symbol [";
      $Sym.prerr_symbol sym;
      prerr "] is applied to static argument(s): {";
      prerr d2a; prerr "}"; prerr_newline ();
      $Err.abort {d2explst n} ()
    end // end of [D2EXPARGsta]
end // end of [d2exparg_dyn_get]

fn symbol_is_unary (sym: sym_t) = begin
  case+ sym of
  | _ when sym = $Sym.symbol_EVALMAC => true
  | _ when sym = $Sym.symbol_LIFTMAC => true
  | _ when sym = $Sym.symbol_TILDA => true
  | _ when sym = $Sym.symbol_IS_NIL => true
  | _ when sym = $Sym.symbol_IS_CONS => true
  | _ when sym = $Sym.symbol_TUP_HEAD => true
  | _ when sym = $Sym.symbol_TUP_TAIL => true
  | _ => false
end

fn symbol_is_binary (sym: sym_t) = begin
  case+ sym of
  | _ when sym = $Sym.symbol_GT => true
  | _ when sym = $Sym.symbol_GTEQ => true
  | _ when sym = $Sym.symbol_LT => true
  | _ when sym = $Sym.symbol_LTEQ => true
  | _ when sym = $Sym.symbol_EQ => true
  | _ when sym = $Sym.symbol_NEQ => true
  | _ when sym = $Sym.symbol_ADD => true
  | _ when sym = $Sym.symbol_SUB => true
  | _ when sym = $Sym.symbol_MUL => true
  | _ when sym = $Sym.symbol_DIV => true
  | _ => false
end // end of [symbol_is_binary]

implement eval0_exp_app_sym
  (loc0, sym, ctx, env, d2as) = let
(*
  val () = begin
    prerr "eval0_exp_app_sym: sym = ";
    $Sym.prerr_symbol sym; prerr_newline ()
  end
*)
  fn err (loc0: loc_t, sym: sym_t): v2alue = begin
    prerr loc0;
    prerr ": error(macro)";
    prerr ": an unrecognized symbol [";
    $Sym.prerr_symbol sym;
    prerr "] is encountered during macro expansion.";
    prerr_newline ();
    $Err.abort {v2alue} ()
  end
in
  case+ sym of
  | _ when symbol_is_binary sym => let
      var d2e10: d2exp? and d2e20: d2exp?
      val () = case+ :(d2e10: d2exp, d2e20: d2exp) => d2as of
        | list_cons (d2a, list_nil ()) => let
            val d2es = d2exparg_dyn_get (loc0, sym, d2a, 2)
            val+ list_cons (d2e1, d2es) = d2es
            val+ list_cons (d2e2, d2es) = d2es
          in
            d2e10 := d2e1; d2e20 := d2e2
          end
        | _ => begin
            prerr loc0; prerr ": error(macro)";
            prerr ": the dynamic symbol ["; $Sym.prerr_symbol sym;
            prerr "] should be applied to exactly two arguments but it is not.";
            prerr_newline ();
            d2e10 := $Err.abort {d2exp} ();
            d2e20 := $Err.abort {d2exp} ();
            $Err.abort {void} ()
          end
      val v2al1 = eval0_exp (loc0, ctx, env, d2e10)
      and v2al2 = eval0_exp (loc0, ctx, env, d2e20)
    in
      case+ sym of
      | _ when sym = $Sym.symbol_GT => begin
          eval0_exp_app_gt (loc0, v2al1, v2al2)
        end
      | _ when sym = $Sym.symbol_GTEQ => begin
          eval0_exp_app_gte (loc0, v2al1, v2al2)
        end
      | _ when sym = $Sym.symbol_LT => begin
          eval0_exp_app_lt (loc0, v2al1, v2al2)
        end
      | _ when sym = $Sym.symbol_LTEQ => begin
          eval0_exp_app_lte (loc0, v2al1, v2al2)
        end
      | _ when sym = $Sym.symbol_EQ => begin
          eval0_exp_app_eq (loc0, v2al1, v2al2)
        end
      | _ when sym = $Sym.symbol_NEQ => begin
          eval0_exp_app_neq (loc0, v2al1, v2al2)
        end
      | _ when sym = $Sym.symbol_ADD => begin
          eval0_exp_app_add (loc0, v2al1, v2al2)
        end
      | _ when sym = $Sym.symbol_SUB => begin
          eval0_exp_app_sub (loc0, v2al1, v2al2)
        end
      | _ when sym = $Sym.symbol_MUL => begin
          eval0_exp_app_mul (loc0, v2al1, v2al2)
        end
(*
      | _ when sym = $Sym.symbol_DIV => begin
          eval0_exp_app_div (loc0, v2al1, v2al2)
        end
*)
      | _ => err (loc0, sym)
    end // [symbol_is_binary]
  | _ when symbol_is_unary sym => let
      var d2e0: d2exp?
      val () = case+ :(d2e0: d2exp) => d2as of
        | list_cons (d2a, list_nil ()) => let
            val d2es = d2exparg_dyn_get (loc0, sym, d2a, 1)
            val list_cons (d2e, d2es) = d2es
          in
            d2e0 := d2e
          end
        | _ => begin
            prerr loc0; prerr ": error(macro)";
            prerr ": the dynamic symbol ["; $Sym.prerr_symbol sym;
            prerr "] should be applied to exactly one argument but it is not.";
            prerr_newline ();
            d2e0 := $Err.abort {d2exp} ();
            $Err.abort {void} ()
          end
      val v2al = eval0_exp (loc0, ctx, env, d2e0)
    in
      case+ sym of
      | _ when sym = $Sym.symbol_EVALMAC => begin
          eval0_exp_app_eval (loc0, v2al)
        end
      | _ when sym = $Sym.symbol_LIFTMAC => begin
          eval0_exp_app_lift (loc0, v2al)
        end
      | _ when sym = $Sym.symbol_TILDA => begin
          eval0_exp_app_neg (loc0, v2al)
        end
      | _ when sym = $Sym.symbol_IS_NIL => begin
          eval0_exp_app_is_nil (loc0, v2al)
        end
      | _ when sym = $Sym.symbol_IS_CONS => begin
          eval0_exp_app_is_cons (loc0, v2al)
        end
      | _ when sym = $Sym.symbol_TUP_HEAD => begin
          eval0_exp_app_tup_head (loc0, v2al)
        end
      | _ when sym = $Sym.symbol_TUP_TAIL => begin
          eval0_exp_app_tup_tail (loc0, v2al)
        end
      | _ => err (loc0, sym)
    end
  | _ => err (loc0, sym)
end // end [eval0_exp_app_sym]

(* ****** ****** *)

fn eval1_d2var
  (loc0: loc_t, env: &alphaenv, d2v: d2var_t)
  : d2var_t = begin
  case+ alphaenv_find (env, d2v) of
  | ~Some_vt d2v_new => d2v_new | ~None_vt () => d2v
end // end of [eval1_d2var]

fn eval1_d2expopt
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, od2e: d2expopt)
  : d2expopt = begin case+ od2e of
  | Some d2e => Some (eval1_d2exp (loc0, ctx, env, d2e))
  | None () => None ()
end // end of [eval1_d2expopt]

fn eval1_d2exparg
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, d2a: d2exparg)
  : d2exparg = begin case+ d2a of
  | D2EXPARGdyn (_(*loc_arg*), npf, d2es) => let
      val d2es = eval1_d2explst (loc0, ctx, env, d2es)
    in
      D2EXPARGdyn (loc0, npf, d2es)
    end
  | D2EXPARGsta _ => d2a
end // end of [eval1_d2exparg]

fun eval1_d2exparglst
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, d2as: d2exparglst)
  : d2exparglst = begin case+ d2as of
  | list_cons (d2a, d2as) => let
      val d2a = eval1_d2exparg (loc0, ctx, env, d2a)
    in
      list_cons (d2a, eval1_d2exparglst (loc0, ctx, env, d2as))
    end
  | list_nil () => list_nil ()
end // end of [eval1_d2exparglst]

fn eval1_i2nvresstate
  (loc0: loc_t, env: &alphaenv, res: i2nvresstate)
  : i2nvresstate = let
  val svs = res.i2nvresstate_svs
  val gua = res.i2nvresstate_gua
  val args = aux (loc0, env, res.i2nvresstate_arg) where {
    fun aux (loc0: loc_t, env: &alphaenv, args: i2nvarglst)
      : i2nvarglst = begin case+ args of
      | list_cons (arg, args) => let
          val d2v = eval1_d2var (loc0, env, arg.i2nvarg_var)
          val arg = i2nvarg_make (d2v, arg.i2nvarg_typ)
        in
          list_cons (arg, aux (loc0, env, args))
        end
      | list_nil () => list_nil ()
    end // end of [aux]
  } // end of [where]
in
  i2nvresstate_make (svs, gua, args)
end // end of [eval1_i2nvresstate]

//

fn eval1_m2atch
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, m2at: m2atch)
  : m2atch = let
  val d2e = eval1_d2exp (loc0, ctx, env, m2at.m2atch_exp)
  val op2t = (
    case+ m2at.m2atch_pat of
    | Some p2t => Some (eval1_p2at (loc0, env, p2t))
    | None () => None ()
  ): p2atopt
in
  m2atch_make (m2at.m2atch_loc, d2e, op2t)
end

fun eval1_m2atchlst
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, m2ats: m2atchlst)
  : m2atchlst = begin case+ m2ats of
  | list_cons (m2at, m2ats) => let
      val m2at = eval1_m2atch (loc0, ctx, env, m2at)
    in
      list_cons (m2at, eval1_m2atchlst (loc0, ctx, env, m2ats))
    end
  | list_nil () => list_nil ()
end // end of [eval1_m2atchlst]

fn eval1_c2lau {n:nat}
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, c2l: c2lau n)
  : c2lau n = let
  val () = alphaenv_push (env)
  val p2ts = eval1_p2atlst (loc0, env, c2l.c2lau_pat)
  val gua = eval1_m2atchlst (loc0, ctx, env, c2l.c2lau_gua)
  val d2e = eval1_d2exp (loc0, ctx, env, c2l.c2lau_exp)
  val () = alphaenv_pop (env)
in
  c2lau_make (c2l.c2lau_loc, p2ts, gua, c2l.c2lau_seq, c2l.c2lau_neg, d2e)
end

fn eval1_c2laulst {n:nat}
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, c2ls: c2laulst n)
  : c2laulst n = let
  fun aux {n:nat} (
      loc0: loc_t
    , ctx: !eval0ctx
    , env: &alphaenv
    , c2ls: c2laulst n
    , res: &c2laulst? >> c2laulst n
    ) : void = begin
    case+ c2ls of
    | list_cons (c2l, c2ls) => let
        val c2l = eval1_c2lau (loc0, ctx, env, c2l)
        val () = (res := list_cons {c2lau n} {0} (c2l, ?))
        val+ list_cons (_, !res_nxt) = res
      in
        aux (loc0, ctx, env, c2ls, !res_nxt); fold@ res
      end
    | list_nil () => (res := list_nil ())
  end // end of [aux]
  var res: c2laulst? // uninitialized
in
  aux (loc0, ctx, env, c2ls, res); res
end

(* ****** ****** *)

implement eval1_d2exp (loc0, ctx, env, d2e0) = begin
  case+ d2e0.d2exp_node of
  | D2Eann_funclo (d2e, fcr) => let
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
    in
      d2exp_ann_funclo (loc0, d2e, fcr)
    end
  | D2Eann_seff (d2e, s2fe) => let
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
    in
      d2exp_ann_seff (loc0, d2e, s2fe)
    end
  | D2Eann_type (d2e, s2e) => let
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
    in
      d2exp_ann_type (loc0, d2e, s2e)
    end
  | D2Eapps (d2e, d2as) => let
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
    in
      case+ d2e.d2exp_node of
      | D2Emac d2m => begin
          if d2mac_kind_get d2m = 0 then begin // [d2m] is short
            // expanding a macro in short form
            eval0_exp_app_mac_short (loc0, d2m, ctx, env, d2as)
          end else begin
            prerr loc0; prerr ": error(macro)";
            prerr ": the dynamic symbol ["; prerr d2m; prerr "] (";
            prerr d2e0.d2exp_loc;
            prerr ") refers to a macro definition in long form";
            prerr "; it should be called inside the syntax ,(...)";
            prerr_newline ();
            $Err.abort {d2exp} ()
          end
        end // end of [D2Emac]
      | _ => let
          val d2as = eval1_d2exparglst (loc0, ctx, env, d2as)
        in
          case+ d2e.d2exp_node of
          | D2Eapps (d2e1, d2as1) => let
              val d2as1 = $Lst.list_append (d2as1, d2as)
            in
              d2exp_apps (loc0, d2e1, d2as1)
            end
          | _ => d2exp_apps (loc0, d2e, d2as)
        end // end of [_]
    end // end of [D2Eapps]
  | D2Earrinit (s2e_elt, od2e_asz, d2es_elt) => let
      val od2e_asz = eval1_d2expopt (loc0, ctx, env, od2e_asz)
      val d2es_elt = eval1_d2explst (loc0, ctx, env, d2es_elt)
    in
      d2exp_arrinit (loc0, s2e_elt, od2e_asz, d2es_elt)
    end // end of [D2Earrinit]
  | D2Earrsize (os2e, d2es) => let
      val d2es = eval1_d2explst (loc0, ctx, env, d2es)
    in
      d2exp_arrsize (loc0, os2e, d2es)
    end // end of [D2Earrsize]
  | D2Earrsub (d2s, d2e_arr, _(*loc*), d2ess_ind) => let
      val d2e_arr = eval1_d2exp (loc0, ctx, env, d2e_arr)
      val d2ess_ind = eval1_d2explstlst (loc0, ctx, env, d2ess_ind)
    in
      d2exp_arrsub (loc0, d2s, d2e_arr, loc0, d2ess_ind)
    end // end of [D2Earrsub]
  | D2Eassgn (d2e1, d2e2) => let
      val d2e1 = eval1_d2exp (loc0, ctx, env, d2e1)
      val d2e2 = eval1_d2exp (loc0, ctx, env, d2e2)
    in
      d2exp_assgn (loc0, d2e1, d2e2)
    end // end of [D2Eassgn]
  | D2Ecaseof (knd, res, n, d2es, c2ls) => let
      val res = eval1_i2nvresstate (loc0, env, res)
      val d2es = eval1_d2explst (loc0, ctx, env, d2es)
      val c2ls = eval1_c2laulst (loc0, ctx, env, c2ls)
    in
      d2exp_caseof (loc0, knd, res, n, d2es, c2ls)
    end // end of [D2Ecaseof]
  | D2Econ (d2c, s2es, npf, d2es) => let
      val d2es = eval1_d2explst (loc0, ctx, env, d2es)
    in
      d2exp_con (loc0, d2c, s2es, npf, d2es)
    end // end of [D2Econ]
  | D2Ecrypt (knd, d2e) => let
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
    in
      d2exp_crypt (loc0, knd, d2e)
    end // end of [D2Ecrypt]
  | D2Edelay (lin, d2e) => let
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
    in
      d2exp_delay (loc0, lin, d2e)
    end // end of [D2Edelay]
  | D2Ederef d2e => let
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
    in
      d2exp_deref (loc0, d2e)
    end // end of [D2Ederef]
  | D2Eeffmask (eff, d2e) => let
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
    in
      d2exp_effmask (loc0, eff, d2e)
    end // end of [D2Eeffmask]
  | D2Eexist (s2as, d2e) => let
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
    in
      d2exp_exist (loc0, s2as, d2e)
    end // end of [D2Eexist]
  | D2Efix (d2v, d2e) => let
      val () = alphaenv_push (env)
      val d2v_new = eval1_d2var (loc0, env, d2v)
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
      val () = alphaenv_pop (env)
    in
      d2exp_fix (loc0, d2v_new, d2e)
    end // end of [D2Efix]
  | D2Efoldat (s2as, d2e) => let
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
    in
      d2exp_foldat (loc0, s2as, d2e)
    end // end of [D2Efoldat]
  | D2Efreeat (s2as, d2e) => let
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
    in
      d2exp_freeat (loc0, s2as, d2e)
    end // end of [D2Efreeat]
  | D2Eif (res, d2e_cond, d2e_then, od2e_else) => let
      val res = eval1_i2nvresstate (loc0, env, res)
      val d2e_cond = eval1_d2exp (loc0, ctx, env, d2e_cond)
      val d2e_then = eval1_d2exp (loc0, ctx, env, d2e_then)
      val od2e_else = eval1_d2expopt (loc0, ctx, env, od2e_else)
    in
      d2exp_if (loc0, res, d2e_cond, d2e_then, od2e_else)
    end // end of [D2Eif]
  | D2Elet (d2cs, d2e) => let
      val () = alphaenv_push (env)
      val d2cs = eval1_d2eclst (loc0, ctx, env, d2cs)
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
      val () = alphaenv_pop (env)
    in
      d2exp_let (loc0, d2cs, d2e)
    end // end of [D2Elet]
  | D2Elst (lin, os2e, d2es) => let
      val d2es = eval1_d2explst (loc0, ctx, env, d2es)
    in
      d2exp_lst (loc0, lin, os2e, d2es)
    end // end of [D2Elst]
  | D2Emacsyn (knd, d2e) => let
      val v2al = (
        case+ knd of
        | $Syn.MACSYNKINDcross () => let
            val v2al = eval0_exp (loc0, ctx, env, d2e)
          in
            V2ALcode (lift_val_exp (loc0, v2al))
          end
        | $Syn.MACSYNKINDdecode () => eval0_exp (loc0, ctx, env, d2e)
        | _ => begin
            prerr loc0; prerr ": error(macro)";
            prerr ": invalid use of macro syntax: ";
            prerr d2e0; prerr_newline ();
            $Err.abort {v2alue} ()
          end
      ) : v2alue
    in
      case+ v2al of
      | V2ALcode d2e_new => d2e_new | _ => begin
          prerr loc0; prerr ": error(macro)";
          prerr ": the expansion of this dynamic expression (";
          prerr d2e.d2exp_loc;
          prerr ") should return a value representing code (abstract syntax tree)";
          prerr ", but it did not do so."; prerr_newline ();
          $Err.abort {d2exp} ()
        end
    end // end of [D2Emacsyn]
  | D2Eptrof (d2e) => let
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
    in
      d2exp_ptrof (loc0, d2e)
    end // end of [D2Eptrof]
  | D2Eraise (d2e) => let
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
    in
      d2exp_raise (loc0, d2e)
    end // end of [D2Eraise]
  | D2Erec (recknd, npf, ld2es) => let
      val ld2es = eval1_labd2explst (loc0, ctx, env, ld2es)
    in
      d2exp_rec (loc0, recknd, npf, ld2es)
    end // end of [D2Erec]
  | D2Eseq d2es => let
      val d2es = eval1_d2explst (loc0, ctx, env, d2es)
    in
      d2exp_seq (loc0, d2es)
    end // end of [D2Eseq]
  | D2Esif (res, s2e_cond, d2e_then, d2e_else) => let
      val res = eval1_i2nvresstate (loc0, env, res)
      val d2e_then = eval1_d2exp (loc0, ctx, env, d2e_then)
      val d2e_else = eval1_d2exp (loc0, ctx, env, d2e_else)
    in
      d2exp_sif (loc0, res, s2e_cond, d2e_then, d2e_else)
    end // end of [D2Esif]
  | D2Estruct ld2es => let
      val ld2es = eval1_labd2explst (loc0, ctx, env, ld2es)
    in
      d2exp_struct (loc0, ld2es)
    end // end of [D2Estruct]
  | D2Etmpid (d2e, ts2ess) => let
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
    in
      d2exp_tmpid (loc0, d2e, ts2ess)
    end // end of [D2Etmpid]
  | D2Evar (d2v) => let
      val d2v_new = eval1_d2var (loc0, env, d2v)
    in
      d2exp_var (loc0, d2v_new)
    end // end of [D2Evar]
  | D2Eviewat (d2e) => let
      val d2e = eval1_d2exp (loc0, ctx, env, d2e)
    in
      d2exp_viewat (loc0, d2e)
    end // end of [D2Eviewat]
(*
  | _ => begin
      prerr loc0;
      prerr ": error(macro)";
      prerr ": unsupported form for macro expansion: ";
      prerr d2e0; prerr_newline ();
      $Err.abort {d2exp} ()
    end // end of [_]
*)
  | _ => d2e0
end // end of [eval1_d2exp]

(* ****** ****** *)

implement eval1_d2explst (loc0, ctx, env, d2es) = let
  fun aux {n:nat} (
      loc0: loc_t
    , ctx: !eval0ctx
    , env: &alphaenv
    , d2es: d2explst n
    , res: &d2explst? >> d2explst n
    ) : void = begin
    case+ d2es of
    | list_cons (d2e, d2es) => let
        val d2e = eval1_d2exp (loc0, ctx, env, d2e)
        val () = (res := list_cons {d2exp} {0} (d2e, ?))
        val+ list_cons (_, !res_nxt) = res
      in
        aux (loc0, ctx, env, d2es, !res_nxt); fold@ res
      end
    | list_nil () => (res := list_nil ())
  end // end of [aux]
  var res: d2explst? // uninitialized
in
  aux (loc0, ctx, env, d2es, res); res
end // end of [eval1_d2explst]

implement eval1_d2explstlst (loc0, ctx, env, d2ess) = begin
  case+ d2ess of
  | list_cons (d2es, d2ess) => let
      val d2es = eval1_d2explst (loc0, ctx, env, d2es)
    in
      list_cons (d2es, eval1_d2explstlst (loc0, ctx, env, d2ess))
    end
  | list_nil () => list_nil ()
end // end of [eval1_d2explstlst]

(* ****** ****** *)

implement eval1_labd2explst (loc0, ctx, env, ld2es) = let
  fun aux (
      loc0: loc_t
    , ctx: !eval0ctx
    , env: &alphaenv
    , ld2es: labd2explst
    , res: &labd2explst? >> labd2explst
    ) : void = begin
    case+ ld2es of
    | LABD2EXPLSTcons (l, d2e, ld2es) => let
        val d2e = eval1_d2exp (loc0, ctx, env, d2e)
        val () = (res := LABD2EXPLSTcons (l, d2e, ?))
        val+ LABD2EXPLSTcons (_, _, !res_nxt) = res
      in
        aux (loc0, ctx, env, ld2es, !res_nxt); fold@ res
      end
    | LABD2EXPLSTnil () => (res := LABD2EXPLSTnil ())
  end // end of [aux]
  var res: labd2explst? // uninitialized
in
  aux (loc0, ctx, env, ld2es, res); res
end // end of [eval1_labd2explst]

(* ****** ****** *)

fun eval1_v2aldeclst
  (loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, d2cs: v2aldeclst)
  : v2aldeclst = let
  val p2ts = aux (loc0, ctx, env, d2cs) where {
    fun aux {n:nat} (
        loc0: loc_t, ctx: !eval0ctx, env: &alphaenv, d2cs: list (v2aldec, n)
      ) : list_vt (p2at, n) = case+ d2cs of
      | list_cons (d2c, d2cs) => let
          val p2t = eval1_p2at (loc0, env, d2c.v2aldec_pat)
        in
          list_vt_cons (p2t, aux (loc0, ctx, env, d2cs))
        end
      | list_nil () => list_vt_nil ()
  } // end of [where]
  val d2cs = aux (loc0, ctx, env, p2ts, d2cs) where {
    fun aux {n:nat} (
        loc0: loc_t, ctx: !eval0ctx, env: &alphaenv,
        p2ts: list_vt (p2at, n), d2cs: list (v2aldec, n)
      ) : list (v2aldec, n) = case+ p2ts of
      | ~list_vt_cons (p2t, p2ts) => let
          val+ list_cons (d2c, d2cs) = d2cs
          val def = eval1_d2exp (loc0, ctx, env, d2c.v2aldec_def)
          val d2c = v2aldec_make (loc0, p2t, def, d2c.v2aldec_ann)
        in
          list_cons (d2c, aux (loc0, ctx, env, p2ts, d2cs))
        end
      | ~list_vt_nil () => list_nil ()
  } // end of [where]
in
  d2cs
end // end of [eval1_v2aldeclst]

(* ****** ****** *)

implement eval1_d2ec (loc0, ctx, env, d2c0) = begin
  case+ d2c0.d2ec_node of
  | D2Cnone () => d2ec_none (loc0)
  | D2Clist d2cs => d2ec_list (loc0, eval1_d2eclst (loc0, ctx, env, d2cs))
  | D2Cvaldecs (knd, d2cs) => let
      val d2cs = eval1_v2aldeclst (loc0, ctx, env, d2cs)
    in
      d2ec_valdecs (loc0, knd, d2cs)
    end
  | D2Cvaldecs_rec (d2cs) => let
      val d2cs = eval1_v2aldeclst (loc0, ctx, env, d2cs)
    in
      d2ec_valdecs_rec (loc0, d2cs)
    end
  | _ => begin
      prerr loc0; prerr ": error(macro)";
      prerr ": this form of declaration (";
      prerr d2c0.d2ec_loc;
      prerr ") is not supported in macro expansion."; prerr_newline ();
      $Err.abort {d2ec} ()
    end
end // end of [eval1_d2ec]

implement eval1_d2eclst (loc0, ctx, env, d2cs) = let
  fun aux (
      loc0: loc_t
    , ctx: !eval0ctx
    , env: &alphaenv
    , d2cs: d2eclst
    , res: &d2eclst? >> d2eclst
    ) : void = begin
    case+ d2cs of
    | list_cons (d2c, d2cs) => let
        val d2c = eval1_d2ec (loc0, ctx, env, d2c)
        val () = (res := list_cons {d2ec} {0} (d2c, ?))
        val+ list_cons (_, !res_nxt) = res
      in
        aux (loc0, ctx, env, d2cs, !res_nxt); fold@ res
      end
    | list_nil () => (res := list_nil ())
  end // end of [aux]
  var res: d2eclst? // uninitialized
in
  aux (loc0, ctx, env, d2cs, res); res
end // end of [eval1_d2eclst]

(* ****** ****** *)

fun eval0ctx_extend_arg {n:nat} (
    loc0: loc_t
  , knd: int (*1/0: long/short*)
  , ctx: !eval0ctx, env: &alphaenv
  , d2vs: d2varlst n, d2es: d2explst n
  , res: eval0ctx
  ) : eval0ctx = let
  fn aux (
      loc0: loc_t
    , ctx: !eval0ctx, env: &alphaenv
    , d2e: d2exp
  ) : v2alue = let
    val d2e = eval1_d2exp (loc0, ctx, env, d2e)
  in
    V2ALcode (d2e)
  end // end of [aux]
  fun auxlst (
    loc0: loc_t
  , ctx: !eval0ctx, env: &alphaenv
  , ld2es: labd2explst
  ) : v2aluelst = begin case+ ld2es of
    | LABD2EXPLSTcons (_(*lab*), d2e, ld2es) => let
        val v2al = aux (loc0, ctx, env, d2e)
      in
        list_cons (v2al, auxlst (loc0, ctx, env, ld2es))
      end
    | LABD2EXPLSTnil () => list_nil ()
  end // end of [auxlst]
in
  case+ d2vs of
  | list_cons (d2v, d2vs) => let
      val+ list_cons (d2e, d2es) = d2es
      val v2al: v2alue = begin case+ knd of
        | 0 (*short*) => begin case+ d2e.d2exp_node of
          | D2Erec (_(*recknd*), _(*npf*), ld2es) => let
              val v2als = auxlst (loc0, ctx, env, ld2es) in V2ALlst v2als
            end // end of [D2Erec]
          | _ => aux (loc0, ctx, env, d2e)
          end // end of [0(*short*)]
        | _ (*long*) => eval0_exp (loc0, ctx, env, d2e)
      end // end of [val]
      val res = eval0ctx_add (res, d2v, v2al)
    in
      eval0ctx_extend_arg (loc0, knd, ctx, env, d2vs, d2es, res)
    end
  | list_nil () => res
end // end of [eval0ctx_extend_arg]

// ------------------------------------

fun eval0ctx_extend_arglst {narg:nat} (
    loc0: loc_t
  , d2m: d2mac_t
  , knd: int (* 1/0: long/short *)
  , ctx: !eval0ctx
  , env: &alphaenv
  , args: list (macarg, narg)
  , d2as: list (d2exparg, narg)
  , res: eval0ctx
  ) : eval0ctx = begin case+ args of
  | list_cons (arg, args) => let
      val+ list_cons (d2a, d2as) = d2as
      var d2es: d2explst = list_nil (); val () = case+ d2a of
        | D2EXPARGdyn (_(*loc*), _(*npf*), d2es1) => d2es := d2es1
        | D2EXPARGsta _ => begin
            prerr loc0; prerr ": error(macro)";
            prerr ": the macro function ["; prerr d2m;
            prerr "] should not be applied to static arguments.";
            prerr_newline ();
            $Err.abort {void} ()
          end
      val d2es = (d2es: d2explst) // handle a complaint by [ATS/Geizella]
      val nd2vs = (case+ arg of
        | MACARGone d2v => @(1, '[d2v]) | MACARGlst (n, d2vs) => @(n, d2vs)
      ) : [n:nat] (int n, d2varlst n)
      val n = nd2vs.0 and d2vs = nd2vs.1
      val nd2es = $Lst.list_length (d2es)
      stavar n: int and nd2es: int
      val n: int n = n and nd2es: int nd2es = nd2es
      val () = ( // arity checking
        if (n <> nd2es) then begin
          prerr loc0; prerr ": error(macro)";
          prerr ": expansion of the macro ["; prerr d2m;
          prerr "] encounters an arity error.";
          prerr_newline ();
          $Err.abort {void} ();
          assert (n = nd2es) // deadcode
        end else begin
          () // [n = nd2es] holds!
        end
      ) : [n == nd2es] void // end of [if]
      val res = eval0ctx_extend_arg (loc0, knd, ctx, env, d2vs, d2es, res)
    in
      eval0ctx_extend_arglst (loc0, d2m, knd, ctx, env, args, d2as, res)
    end
  | list_nil () => res
end // end of [eval0ctx_extend_arglst]

implement // expanding macros in long form
  eval0_exp_app_mac_long {narg} (loc0, d2m, ctx, env, d2as) = let
(*
  val () = begin
    prerr "eval0_exp_app_mac_long: d2m = "; prerr d2m; prerr_newline ()
  end
*)
  val narg = d2mac_narg_get (d2m); val args = d2mac_arglst_get (d2m)
  stavar nd2as: int; val nd2as: int nd2as = $Lst.list_length d2as
(*
  val () = begin
    prerr "eval0_exp_app_mac_long: narg = "; prerr narg; prerr_newline ();
    prerr "eval0_exp_app_mac_long: nd2as = "; prerr nd2as; prerr_newline ();
  end
*)
  val () = ( // checking for improper application
    if narg <> nd2as then begin
      prerr loc0; prerr ": error(macro)";
      prerr ": the macro function ["; prerr d2m;
      if narg > nd2as then prerr "] is applied insufficiently.";
      if nd2as < narg then prerr "] is overly applied.";
      prerr_newline ();
      $Err.abort {void} ();
      assert (narg = nd2as) // deadcode
    end else begin
      () // [narg = nd2as] holds!
    end
  ) : [narg==nd2as] void // end of [if]
  val ctx_new = eval0ctx_extend_arglst (
    loc0, d2m, 1(*long*), ctx, env, args, d2as, EVAL0CTXnil ()
  ) // end of [eval0ctx_extend_arglst]
(*
  val () = begin
    prerr "eval0_exp_app_mac_long: ctx_new = "; prerr_newline (); prerr ctx_new
  end
*)
  val v2al = eval0_exp (loc0, ctx_new, env, d2mac_def_get d2m)
  val () = eval0ctx_free ctx_new
in
  v2al
end // end of [eval0_exp_app_mac_long]

(* ****** ****** *)

implement // expanding macros in short form
  eval0_exp_app_mac_short {narg} (loc0, d2m, ctx, env, d2as) = let
(*
  val () = begin
    prerr "eval0_exp_app_mac_short: d2m = "; prerr d2m; prerr_newline ()
  end
*)
  val narg = d2mac_narg_get (d2m)
  val args = d2mac_arglst_get (d2m)
  stavar nd2as: int; val nd2as: int (nd2as) = $Lst.list_length d2as
(*
  val () = begin
    prerr "eval0_exp_app_mac_short: narg = "; prerr narg; prerr_newline ();
    prerr "eval0_exp_app_mac_short: nd2as = "; prerr nd2as; prerr_newline ();
  end
*)
  val () = (
    if narg > nd2as then begin
      prerr loc0; prerr ": error(macro)";
      prerr ": the macro function ["; prerr d2m;
      prerr "] is applied insufficiently."; prerr_newline ();
      $Err.abort {void} ();
      assert (narg <= nd2as) // deadcode
    end else begin
      () // [narg <= nd2as] holds!
    end
  ) : [narg <= nd2as] void // end of [if]
  var d2as2: d2exparglst = d2as
  val d2as1 = aux (narg, d2as2) where {
    fun aux {i1, i2:nat | i1 <= i2} 
      (i1: int i1, d2as: &list (d2exparg, i2) >> list (d2exparg, i2-i1))
      : list (d2exparg, i1) =
      if i1 > 0 then let
        val+ list_cons (d2a1, d2as1) = d2as; val () = d2as := d2as1
      in
        list_cons (d2a1, aux (i1-1, d2as))
      end else begin
        list_nil ()
      end // end of [aux]
  }
  val ctx_new = eval0ctx_extend_arglst (
    loc0, d2m, 0(*short*), ctx, env, args, d2as1, EVAL0CTXnil ()
  ) // end of [eval0ctx_extend_arglst]
(*
  val () = begin
    prerr "eval0_exp_app_mac_short: ctx_new =\n"; prerr ctx_new
  end
*)
  val d2e = eval1_d2exp (loc0, ctx_new, env, d2mac_def_get d2m)
  val () = eval0ctx_free ctx_new
in
  case+ d2as2 of
  | list_cons _ => begin case+ d2e.d2exp_node of
    | D2Eapps (d2e_fun, d2as1) => let
        val d2as_arg = $Lst.list_append (d2as1, d2as2)
      in
        d2exp_apps (loc0, d2e_fun, d2as_arg)
      end
    | _ =>  d2exp_apps (loc0, d2e, d2as2)
    end
  | list_nil () => d2e
end // end of [eval0_exp_app_mac_short]

(* ****** ****** *)

implement macro_eval_cross (d2e) = let
  val loc0 = d2e.d2exp_loc
  var ctx = EVAL0CTXnil ()
  var env = ALPHAENVnil ()
  val v2al = eval0_exp (loc0, ctx, env, d2e)
  val () = alphaenv_free (env)
  val () = eval0ctx_free (ctx)
in
  lift_val_exp (loc0, v2al)
end // end of [macro_eval_cross]

implement macro_eval_decode (d2e) = let
  val loc0 = d2e.d2exp_loc
  var ctx = EVAL0CTXnil ()
  var env = ALPHAENVnil ()
  val v2al = eval0_exp (loc0, ctx, env, d2e)
  val () = alphaenv_free (env)
  val () = eval0ctx_free (ctx)
in
  case+ v2al of
  | V2ALcode d2e_new => d2e_new
  | _ => begin
      prerr d2e.d2exp_loc; prerr ": error(macro)";
      prerr ": the expansion of this macro should yield code (abstract syntax tree)";
      prerr ", but a value that does not represent code is returned instead.";
      prerr_newline ();
      $Err.abort {d2exp} ()
    end
end // end of [macro_eval]

(* ****** ****** *)

implement macro_eval_app_short (loc0, d2m, d2as) = let
  var ctx = EVAL0CTXnil ()
  var env = ALPHAENVnil ()
  val d2e = eval0_exp_app_mac_short (loc0, d2m, ctx, env, d2as)
  val () = alphaenv_free (env)
  val () = eval0ctx_free (ctx)
in
  d2e
end // end of [macro_eval_app_short]

(* ****** ****** *)

(* end of [ats_macro.dats] *)
