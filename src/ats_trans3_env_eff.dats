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

(* Mainly for tracking effects during the third translation *)

(* ****** ****** *)

staload Eff = "ats_effect.sats"
staload Err = "ats_error.sats"
staload Lst = "ats_list.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

datatype effenvitem = (* effect environment item *)
  | EFFENVITEMeff of $Syn.effect_t
  | EFFENVITEMeffmask of $Syn.effect_t
  | EFFENVITEMlam of s2eff

typedef effenvitemlst = List effenvitem
typedef effenvitemlstlst = List effenvitemlst

extern
fun fprint_effenvitem {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, efi: effenvitem): void

extern
fun fprint_effenvitemlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, efis: effenvitemlst): void

extern
fun fprint_effenvitemlstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, efiss: effenvitemlstlst): void

(* ****** ****** *)

implement fprint_effenvitem (pf | out, efi) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ efi of
  | EFFENVITEMeff eff => begin
      strpr "EFFENVeff("; $Eff.fprint_effect (pf | out, eff); strpr ")"
    end
  | EFFENVITEMeffmask eff => begin
      strpr "EFFENVeffmask("; $Eff.fprint_effect (pf | out, eff); strpr ")"
    end
  | EFFENVITEMlam s2fe => begin
      strpr "EFFENVeff("; fprint_s2eff (pf | out, s2fe); strpr ")"
    end
end // end of [fprint_effenvitem]

implement fprint_effenvitemlst {m} (pf | out, efis) = let
  fun aux (out: &FILE m, i: int, efis: effenvitemlst): void =
    case+ efis of
    | list_cons (efi, efis) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_effenvitem (pf | out, efi); aux (out, i + 1, efis)
      end
    | list_nil () => ()
in
  aux (out, 0, efis)
end // end of [fprint_effenvitemlst]

implement fprint_effenvitemlstlst {m} (pf | out, efiss) = let
  fun aux (out: &FILE m, i: int, efiss: effenvitemlstlst): void =
    case+ efiss of
    | list_cons (efis, efiss) => begin
        if i > 0 then fprint1_string (pf | out, "; ");
        fprint_effenvitemlst (pf | out, efis); aux (out, i + 1, efiss)
      end
    | list_nil () => ()
in
  aux (out, 0, efiss)
end // end of [fprint_effenvitemlstlst]

(* ****** ****** *)

local

assume effect_env_token = unit_v

typedef eff_t = $Syn.effect_t
typedef efs_t = $Eff.effset_t

val the_efis = ref_make_elt<effenvitemlst> (list_nil)
val the_efiss = ref_make_elt<effenvitemlstlst> (list_nil)

in

implement the_effect_env_add_lam (s2fe) = begin
  !the_efis := list_cons (EFFENVITEMlam s2fe, !the_efis)
end // end of [the_effect_env_add_lam]

implement the_effect_env_add_eff (eff) = begin
  !the_efis := list_cons (EFFENVITEMeff eff, !the_efis)
end // end of [the_effect_env_add_eff]

implement the_effect_env_pop (pf | (*none*)) = let
  prval unit_v () = pf in case+ !the_efiss of
  | list_cons (efis, efiss) => begin
      !the_efis := efis; !the_efiss := efiss
    end
  | list_nil () => begin
      prerr "Internal Error: the_effect_env_pop";
      prerr_newline ();
      $Err.abort {void} ()
    end
end // end of [the_effect_env_pop]

implement the_effect_env_push () = begin
  !the_efiss := list_cons (!the_efis, !the_efiss);
  (unit_v () | ())
end // end of [the_effect_env_push]

implement the_effect_env_push_lam (s2fe) = begin
  !the_efiss := list_cons (!the_efis, !the_efiss);
  !the_efis := list_cons (EFFENVITEMlam s2fe, !the_efis);
  (unit_v () | ())
end // end of [the_effect_env_push_lam]

implement the_effect_env_push_delay () = let
  val efis = !the_efis
  val () = !the_efiss := list_cons (efis, !the_efiss)
  val efis = list_cons (EFFENVITEMeff $Eff.effect_ref, efis)
in
  !the_efis := efis; (unit_v () | ())
end // end of [the_effect_env_push_delay]

implement the_effect_env_push_eff (effs) = let
  val efis = !the_efis
  val () = !the_efiss := list_cons (efis, !the_efiss)
  val () = !the_efis := aux (effs, efis) where {
    fun aux (effs: $Syn.effectlst, efis: effenvitemlst)
      : effenvitemlst = case+ effs of
      | list_cons (eff, effs) => begin
          aux (effs, list_cons (EFFENVITEMeff eff, efis))
        end
      | list_nil () => efis
  } // end of [where]
in
  (unit_v () | ())
end // end of [the_effect_env_push_eff]

implement the_effect_env_push_effmask (effs) = let
  val efis = !the_efis
  val () = !the_efiss := list_cons (efis, !the_efiss)
  val () = !the_efis := aux (effs, efis) where {
    fun aux (effs: $Syn.effectlst, efis: effenvitemlst)
      : effenvitemlst = case+ effs of
      | list_cons (eff, effs) => begin
          aux (effs, list_cons (EFFENVITEMeffmask eff, efis))
        end
      | list_nil () => efis
  } // end of [where]
in
  (unit_v () | ())
end // end of [the_effect_env_push_effmask]

(* ****** ****** *)

overload = with $Eff.eq_effect_effect

fn the_effect_env_check_eff_err (eff0: eff_t): int = let
(*
  val () = begin
    print "the_effect_env_check_eff_err: eff0 = "; print eff0; print_newline ()
  end
*)
  fun aux (eff0: eff_t, efis: effenvitemlst): int =
    case+ efis of
    | list_cons (efi, efis) => begin case+ efi of
      | EFFENVITEMeff eff => begin
          if eff0 = eff then 1 else aux (eff0, efis)
        end
      | EFFENVITEMeffmask eff => begin
          if eff0 = eff then 0 else aux (eff0, efis)
        end
      | EFFENVITEMlam s2fe => begin
          if s2eff_contain_eff (s2fe, eff0) then 0 else 1
        end
      end
    | list_nil () => 0
in
  aux (eff0, !the_efis)
end // end of [the_effect_env_check_eff]

fn the_effect_env_check_eff
  (loc0: loc_t, eff0: eff_t): void = begin
  if the_effect_env_check_eff_err (eff0) > 0 then begin
    $Loc.prerr_location loc0;
    prerr ": error(3)";
    prerr ": the effect [";
    $Eff.prerr_effect eff0;
    prerr "] is disallowed.";
    prerr_newline ();
    $Err.abort {void} ()
  end
end // end of [the_effect_env_check_eff]

implement the_effect_env_check_exn (loc0) =
  the_effect_env_check_eff (loc0, $Eff.effect_exn)

implement the_effect_env_check_ntm (loc0) =
  the_effect_env_check_eff (loc0, $Eff.effect_ntm)

implement the_effect_env_check_ref (loc0) =
  the_effect_env_check_eff (loc0, $Eff.effect_ref)

//

fn the_effect_env_check_effset (loc0: loc_t, efs0: efs_t): void = let
  fun auxCK (effs: List eff_t):<cloptr1> List eff_t = begin
    case+ effs of
    | list_cons (eff, effs) => begin
        if $Eff.effset_contain (efs0, eff) then
          let val err = the_effect_env_check_eff_err (eff) in
            if err > 0 then list_cons (eff, auxCK effs) else auxCK effs
          end
        else auxCK effs
      end
    | list_nil () => list_nil ()
  end // end of [auxCK]
  val err = auxCK ($Eff.effectlst_all)
  val nerr = aux (err, 0) where { // [nerr] is the length of [err]
    fun aux (xs: List eff_t, i: int): int = case+ xs of
      | list_cons (_, xs) => aux (xs, i+1) | list_nil () => i
  } // end of [where]
  fun auxPR (i: int, effs: List eff_t): void =
    case+ effs of
    | list_cons (eff, effs) => begin
        if i > 0 then prerr ", "; $Eff.prerr_effect eff; auxPR (i+1, effs)
      end
    | list_nil () => ()
  val () =
    if nerr > 0 then begin
      $Loc.prerr_location loc0;
      prerr ": error(3)";
      if nerr <= 1 then prerr ": the effect [" else prerr ": the effects [";
    end
  val () = if nerr > 0 then auxPR (0, err)
in
  if nerr > 0 then begin
    if nerr <= 1 then prerr "] is disallowed." else prerr "] are disallowed.";
    prerr_newline ();
    $Err.abort {void} ()
  end
end // end of [the_effect_env_check_effset]

implement the_effect_env_check_all (loc0) =
  the_effect_env_check_effset (loc0, $Eff.effset_all)

//

implement the_effect_env_check_effvar (loc0, s2v0) = let
(*
  val () = begin
    print "effect_env_check_var: s2v0 = "; print s2v0; print_newline ()
  end
*)
  fun aux (s2v0: s2var_t, efis: effenvitemlst): bool =
    case+ efis of
    | list_cons (efi, efis) => begin case+ efi of
      | EFFENVITEMeff eff => false
      | EFFENVITEMeffmask eff => aux (s2v0, efis)
      | EFFENVITEMlam s2fe => s2eff_contain_effvar (s2fe, s2v0)
      end
    | list_nil () => true
in
  if aux (s2v0, !the_efis) then () else begin
    $Loc.prerr_location loc0;
    prerr ": error(3)";
    prerr ": the effect ["; prerr s2v0; prerr "] is disallowed";
    prerr_newline ();
    $Err.abort {void} ();
  end
end // end of [the_effect_env_check_effvar]

fun the_effect_env_check_sexp
  (loc0: loc_t, s2e0: s2exp): void = let
  val s2e0 = s2exp_whnf s2e0 in case+ s2e0.s2exp_node of
    | S2Eeff s2fe => the_effect_env_check_seff (loc0, s2fe)
    | S2Evar s2v => the_effect_env_check_effvar (loc0, s2v)
    | _ => begin
        $Loc.prerr_location loc0;
        prerr ": Internal Error: the_effect_env_check_s2exp: s2e0 = ";
        prerr s2e0;
        prerr_newline ();
        $Err.abort {void} ()
      end
end // end of [the_effect_env_check_sexp]

and the_effect_env_check_sexplst
  (loc0: loc_t, s2es: s2explst): void = begin
  case+ s2es of
  | list_cons (s2e, s2es) => begin
      the_effect_env_check_sexp (loc0, s2e);
      the_effect_env_check_sexplst (loc0, s2es)
    end
  | list_nil () => ()
end // end of [the_effect_env_check_sexplst]

implement the_effect_env_check_seff (loc0, s2fe0) = let
(*
  val () = begin
    print "the_effect_env_check_seff: s2fe0 = "; print s2fe0; print_newline ()
  end
*)
in
  case+ s2fe0 of
  | S2EFFall () => the_effect_env_check_all loc0
  | S2EFFnil () => ()
  | S2EFFset (efs, s2es) => begin
      the_effect_env_check_effset (loc0, efs);
      the_effect_env_check_sexplst (loc0, s2es)
    end
end // end of [the_effect_env_check_seff]

end // end of [local]

(* ****** ****** *)

(* end of [ats_trans3_env_eff.dats] *)
