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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October 2007

(* ****** ******* *)

staload Fix = "ats_fixity.sats"
staload Sym = "ats_symbol.sats"
staload SymEnv = "ats_symenv.sats"

(* ****** ******* *)

staload "ats_dynexp1.sats"
staload "ats_staexp1.sats"
staload "ats_trans1_env.sats"

(* ****** ******* *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ******* *)

staload _(*anonymous*) = "ats_map_lin.dats"
staload _(*anonymous*) = "ats_symenv.dats"

(* ****** ******* *)

typedef sym_t = $Sym.symbol_t
typedef symenv_t (itm:t@ype) = $SymEnv.symenv_t itm

(* ****** ******* *)

fn prerr_interror () = prerr "INTERNAL ERROR (ats_trans1_env)"

(* ****** ******* *)

typedef e1xpenv = symenv_t (e1xp)

val the_e1xpenv = $SymEnv.symenv_make {e1xp} ()

implement the_e1xpenv_add (opr, e1xp) = let
(*
  val () = begin
    print "e1xp_add: opr = "; print opr; print_newline ()
  end // end of [val]
*)
in
  $SymEnv.symenv_insert_fst (the_e1xpenv, opr, e1xp)
end // end of [the_e1xpenv_add]

implement the_e1xpenv_find (opr) = let
(*
  val () = begin
    print "e1xp_find: opr = "; print opr; print_newline ()
  end // end of [val]
*)
in
  $SymEnv.symenv_search_all (the_e1xpenv, opr)
end // end of [the_e1xpenv_find]

(* ****** ****** *)

typedef fxtyenv = symenv_t (fxty_t)

val the_fxtyenv = $SymEnv.symenv_make {fxty_t} ()

implement the_fxtyenv_add (opr, fxty) = let
  val ans = $SymEnv.symenv_remove_fst (the_fxtyenv, opr)
  val () =
    case+ ans of ~Some_vt _ => () | ~None_vt () => ()
  // end of [val]
in
  $SymEnv.symenv_insert_fst (the_fxtyenv, opr, fxty)
end // end of [the_fxtyenv_add]

implement the_fxtyenv_find (opr) = let
  val ans = $SymEnv.symenv_search_all (the_fxtyenv, opr)
in
  case+ ans of
  | ~None_vt () => begin
      $SymEnv.symenv_pervasive_search (the_fxtyenv, opr)
    end
  | Some_vt _ => (fold@ ans; ans)
end // end of [the_fxtyenv_find]

implement the_fxtyenv_pervasive_add_topenv () = let
  val m = $SymEnv.symenv_top_get (the_fxtyenv)
in
  $SymEnv.symenv_pervasive_add (the_fxtyenv, m)
end // end of [fxtyenv_pervasive_add_topenv]

(* ****** ****** *)

implement ats_fxtyenv_print () = let
  val r_m = $SymEnv.symenv_reftop_get the_fxtyenv
  val kis = $SymEnv.symmap_reflist_get (r_m)
  typedef ki = @(sym_t, fxty_t)
  fun loop {n:nat} .<n>.
    (kis: list_vt (ki, n)): void = begin case+ kis of
    | ~list_vt_cons (ki, kis) => let
        val (k, i) = ki; val () = begin
          $Sym.print_symbol_code k; print " = "; $Fix.print_fxty i;
          print_newline ()
        end // end of [val]
      in
        loop (kis)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => ()
  end (* end of [loop] *)
in
  loop kis
end // end of [ats_fxtyenv_print]

(* ****** ****** *)

local

assume trans1_level_token = unit_v
val the_trans1_level : ref int = ref_make_elt<int> 0

in // in of [local]

implement trans1_level_get () = !the_trans1_level

implement trans1_level_dec (pf | (*none*)) = let
  prval unit_v () = pf in
  !the_trans1_level := !the_trans1_level - 1
end // end of [trans1_level_dec]

implement trans1_level_inc () = let
  val () = !the_trans1_level := !the_trans1_level + 1 in
  (unit_v () | ())
end // end of [trans1_level_inc]

end // end of [local]

(* ****** ******* *)

implement trans1_env_pop () = begin
  $SymEnv.symenv_pop (the_e1xpenv);
  $SymEnv.symenv_pop (the_fxtyenv);
end // end of [trans1_env_pop]

implement trans1_env_push () = begin
  $SymEnv.symenv_push (the_e1xpenv);
  $SymEnv.symenv_push (the_fxtyenv)
end // end of [trans1_env_push]

implement trans1_env_localjoin () = begin
  $SymEnv.symenv_localjoin (the_e1xpenv);
  $SymEnv.symenv_localjoin (the_fxtyenv)
end // end of [trans1_env_localjoin]

implement trans1_env_save () = begin
  $SymEnv.symenv_save (the_e1xpenv);
  $SymEnv.symenv_save (the_fxtyenv)
end // end of [trans1_env_save]

implement trans1_env_restore () = begin
  $SymEnv.symenv_restore (the_e1xpenv);
  $SymEnv.symenv_restore (the_fxtyenv)
end // end of [trans1_env_restore]

(* ****** ****** *)

staload HT = "ats_hashtbl.sats"
staload HASHTBL = "ats_hashtbl.dats"

local

val SIZE_HINT = 7
val theHashTable = begin
  $HT.hashtbl_str_make_hint (SIZE_HINT): $HT.hashtbl_t (string, d1eclst)
end // end of [val]

in // in of [local]

implement staload_file_insert (fullname, d1cs) = let
  val ans = $HT.hashtbl_insert (theHashTable, fullname, d1cs)
in
  case+ ans of
  | ~Some_vt (d1c) => begin
      prerr_interror ();
      prerr ": [staload_file_insert] failed."; prerr_newline ();
      exit {void} (1)
    end // end of [Some_vt]
  | ~None_vt () => ()
end // end of [staload_file_insert]

implement staload_file_search (fullname) =
  $HT.hashtbl_search (theHashTable, fullname)

end // end of [local]

(* ****** ****** *)

(* end of [ats_trans1_env.dats] *)
