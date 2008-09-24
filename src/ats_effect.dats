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

// Time: August 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

(* ats_effect: for handing effects *)

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_effect.sats"

(* ****** ****** *)

#define nil list_nil
#define :: list_cons
#define cons list_cons

(* ****** ****** *)

typedef t0kn = $Syn.t0kn
typedef funclo = $Syn.funclo
typedef loc_t = $Loc.location_t

(* ****** ****** *)

overload prerr with $Loc.prerr_location

(* ****** ****** *)

typedef effect = int
assume $Syn.effect_t = effect
extern typedef "ats_effect_t" = effect

// the maximal effect number
#define MAX_EFFECT_NUMBER 3
// #assert (MAX_EFFECT_NUMBER <= __WORDSIZE)

macdef EFFexn = 1 // exception
macdef EFFntm = 2 // nontermination
macdef EFFref = 3 // reference

implement effect_exn = EFFexn
implement effect_ntm = EFFntm
implement effect_ref = EFFref
implement effectlst_all = '[ EFFexn, EFFntm, EFFref ]

implement eq_effect_effect (eff1: effect, eff2: effect): bool =
  eq_int_int (eff1, eff2)

//

implement fprint_effect (pf | out, eff) = begin
  if eq_int_int (eff, EFFexn) then fprint (pf | out, "exn")
  else if eq_int_int (eff, EFFntm) then fprint (pf | out, "ntm")
  else if eq_int_int (eff, EFFref) then fprint (pf | out, "ref")
  else begin
    fprint (pf | out, "eff(");
    fprint_int (pf | out, eff);
    fprint (pf | out, ")")
  end
end // end of [fprint_effect]

implement fprint_effectlst {m} (pf | out, effs) = let
  fun aux (i: int, out: &FILE m, effs: effectlst): void =
    case+ effs of
    | list_cons (eff, effs) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_effect (pf | out, eff); aux (i+1, out, effs)
      end
    | list_nil () => ()
in
  aux (0, out, effs)
end // end of [fprint_effectlst]

(* ****** ****** *)

implement print_effect (eff) = print_mac (fprint_effect, eff)
implement prerr_effect (eff) = prerr_mac (fprint_effect, eff)

(* ****** ****** *)

typedef effset = uint

assume effset_t = effset
extern typedef "ats_effset_t" = effset

macdef effset_exn = 0x1 // exception
macdef effset_ntm = 0x2 // nontermination
macdef effset_ref = 0x4 // reference

implement effset_all = uint_of ((1 << MAX_EFFECT_NUMBER) - 1)
implement effset_nil = uint_of_int 0

implement eq_effset_effset (efs1, efs2) = eq_uint_uint (efs1, efs2)

%{

#define MAX_EFFECT_NUMBER 4

#ifdef __WORDSIZE

#if (MAX_EFFECT_NUMBER > __WORDSIZE)
#error "MAX_EFFECT_NUMBER is too large!"
#endif

#endif

ats_void_type
ats_effect_fprint_effset (ats_ptr_type out, ats_effset_t effs) {
  int i, n ;

  i = 1 ; n = 0 ;
  while (i <= MAX_EFFECT_NUMBER) {
    if (effs & 0x1) {
      if (n > 0) fprintf ((FILE *)out, ",");
      ats_effect_fprint_effect (out, i) ; ++n ;
    }
    ++i ; effs >>= 1 ;
  }

  return ;
}

%}

(* ****** ****** *)

%{

ats_effset_t
ats_effect_effset_add (ats_effset_t efs, ats_effect_t eff) {
  unsigned int i = 1 ;
  while (eff > 1) { i <<= 1; --eff ; }
  return (efs | i) ;
}

ats_effset_t
ats_effect_effset_del (ats_effset_t efs, ats_effect_t eff) {
  unsigned int i = 1 ;
  while (eff > 1) { i <<= 1; --eff ; }
  return (efs & ~i) ;
}

ats_bool_type
ats_effect_effset_contain (ats_effset_t efs, ats_effect_t eff) {
  unsigned int i = 1 ;
  while (eff > 1) { i <<= 1; --eff ; }
  return (efs & i ? ats_true_bool : ats_false_bool) ;
}

ats_effset_t
ats_effect_effset_union (ats_effset_t efs1, ats_effset_t efs2) {
  return (efs1 | efs2) ;
}

ats_bool_type
ats_effect_effset_subset (ats_effset_t efs1, ats_effset_t efs2) {
  return (efs1 & ~efs2 ? ats_false_bool : ats_true_bool) ;
}

%}

(* ****** ****** *)

implement $Syn.d0exp_effmask_all (t: t0kn) = '{
  d0exp_loc= t.t0kn_loc, d0exp_node= $Syn.D0Eeffmask effectlst_all
}

implement $Syn.d0exp_effmask_exn (t: t0kn) = '{
  d0exp_loc= t.t0kn_loc, d0exp_node= $Syn.D0Eeffmask '[effect_exn]
}

implement $Syn.d0exp_effmask_ntm (t: t0kn) = '{
  d0exp_loc= t.t0kn_loc, d0exp_node= $Syn.D0Eeffmask '[effect_ntm]
}

implement $Syn.d0exp_effmask_ref (t: t0kn) = '{
  d0exp_loc= t.t0kn_loc, d0exp_node= $Syn.D0Eeffmask '[effect_ref]
}

(* ****** ****** *)

val effvars_nil: effvarlst = nil ()

fun fprint_effvarlst {m:file_mode} (
    pf: file_mode_lte (m,w)
  | out: &FILE m
  , evs: effvarlst
  ) : void = let
  fun aux (out: &FILE m, i: int, evs: effvarlst): void =
    case+ evs of
    | cons (ev, evs) => begin
        if i > 0 then fprint (pf | out, ", ");
        $Syn.fprint_i0de (pf | out, ev); aux (out, i+1, evs)
      end
    | nil () => ()
in
  aux (out, 0, evs)
end // end of [fprint_effvarlst]

implement fprint_effcst (pf | out, efc) = begin case+ efc of
  | EFFCSTall () => fprint (pf | out, "all")
  | EFFCSTnil () => fprint (pf | out, "nil")
  | EFFCSTset (es, evs) => begin
      fprint (pf | out, "set(");
      fprint_effset (pf | out, es);
      fprint (pf | out, "; ");
      fprint_effvarlst (pf | out, evs);
      fprint (pf | out, ")")
    end
end // end of [fprint_effcst]

(* ****** ****** *)

implement print_effcst (efc) = print_mac (fprint_effcst, efc)
implement prerr_effcst (efc) = prerr_mac (fprint_effcst, efc)

(* ****** ****** *)

implement effcst_contain (efc, eff) = begin
  case+ efc of
  | EFFCSTall () => true
  | EFFCSTnil () => false
  | EFFCSTset (efs, evs)  => effset_contain (efs, eff)
end // end of [effcst_contain]

implement effcst_contain_ntm efc = effcst_contain (efc, EFFntm)

(* ****** ****** *)

fn name_is_emp (name: string): bool = name = "0"

fn name_is_all (name: string): bool = name = "1"

fn name_is_exn (name: string): bool =
  if name = "exn" then true else name = "exception"

fn name_is_exnref (name: string): bool = name = "exnref"

fn name_is_gc (name: string): bool = name = "gc"

fn name_is_heap (name: string): bool =
  if name = "hp" then true else name = "heap"

fn name_is_ntm (name: string): bool =
  if name = "ntm" then true else name = "nonterm"

fn name_is_ref (name:string): bool =
  if name = "ref" then true else name = "reference"

fn name_is_term (name: string): bool =
  name = "term"

fn name_is_write (name: string): bool =
  if name = "wrt" then true else name = "write"

(* ****** ****** *)

local

fn loop_err (loc: loc_t, name: string): void = begin
  prerr loc;
  prerr ": error(1): unrecognized effect constant: ["; prerr name; prerr "]";
  prerr_newline ();
  $Err.abort ()
end // end of [loop_err]

fun loop (
    fc: &funclo
  , lin: &int
  , prf: &int
  , efs: &effset
  , evs: &effvarlst
  , tags: $Syn.e0fftaglst
  ) : void = begin case+ tags of
  | cons (tag, tags) => let
      val () = begin
        case+ tag.e0fftag_node of
        | $Syn.E0FFTAGvar ev => evs := cons (ev, evs)
        | $Syn.E0FFTAGcst (isneg, name) when name_is_all name => begin
            if isneg > 0 then efs := effset_nil else efs := effset_all;
            evs := effvars_nil
          end
        | $Syn.E0FFTAGcst (isneg, name) when name_is_emp name => begin
            if isneg > 0 then efs := effset_all else efs := effset_nil;
            evs := effvars_nil
          end
        | $Syn.E0FFTAGcst (isneg, name) => begin case+ name of
          | _ when name_is_exn name => begin
              if isneg > 0 then
                efs := effset_del (efs, EFFexn)
              else
                efs := effset_add (efs, EFFexn)
            end
          | _ when name_is_exnref name => begin
              if isneg > 0 then
                efs := effset_del (effset_del (efs, EFFexn), EFFref)
              else
                efs := effset_add (effset_add (efs, EFFexn), EFFref)
            end
          | _ when name_is_ntm name => begin
              if isneg > 0 then
                efs := effset_del (efs, EFFntm)
              else
                efs := effset_add (efs, EFFntm)
            end
          | _ when name_is_term name => begin
              if isneg > 0 then
                efs := effset_add (efs, EFFntm)
              else
                efs := effset_del (efs, EFFntm)
            end
          | _ when name_is_ref name => begin
              if isneg > 0 then
                efs := effset_del (efs, EFFref)
              else
                efs := effset_add (efs, EFFref)
            end
          | _ => loop_err (tag.e0fftag_loc, name)
          end
        | $Syn.E0FFTAGprf () => prf := 1
        | $Syn.E0FFTAGlin i => begin
            if i > 0 then begin
              lin := 1; efs := effset_all; evs := effvars_nil
            end else begin
              lin := 1
            end
          end
        | $Syn.E0FFTAGfun i(*nil/all*) => begin
            if i > 0 then begin
              fc := $Syn.FUNCLOfun (); efs := effset_all; evs := effvars_nil
            end else begin
              fc := $Syn.FUNCLOfun ()
            end
          end
        | $Syn.E0FFTAGclo (knd(*1/~1:ptr/ref*), i(*nil/all*)) => begin
            if i > 0 then begin
              fc := $Syn.FUNCLOclo (knd); efs := effset_all; evs := effvars_nil
            end else begin
              fc := $Syn.FUNCLOclo (knd)
            end
          end
        end // end of [case]
    in
      loop (fc, lin, prf, efs, evs, tags)
    end
  | nil () => ()
end // end of [loop]

in // in of [local]

implement e0fftaglst_tr (fc0, tags) = let
  var fc: funclo = fc0
  var lin: int = 0 and prf: int = 0
  var efs: effset = effset_nil and evs: effvarlst = effvars_nil
  val () = loop (fc, lin, prf, efs, evs, tags)
  val efc =
    if eq_effset_effset (efs, effset_all) then EFFCSTall ()
    else if eq_effset_effset (efs, effset_nil) then begin
      case+ evs of nil () => EFFCSTnil () | _ => EFFCSTset (efs, evs)
    end else EFFCSTset (efs, evs)
in
  @(fc, lin, prf, efc)
end // end of [e0fftaglst_tr]

end // end of [local]

(* ****** ****** *)

(* end of [ats_effect.dats] *)
