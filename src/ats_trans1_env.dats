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

// Time: October 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ******* *)

staload Fix = "ats_fixity.sats"
staload Sym = "ats_symbol.sats"
staload SymEnv = "ats_symenv.sats"

(* ****** ******* *)

staload "ats_reference.sats"

(* ****** ******* *)

staload "ats_dynexp1.sats"
staload "ats_staexp1.sats"
staload "ats_trans1_env.sats"

(* ****** ******* *)

staload _(*anonymous*) = "ats_map_lin.dats"
staload _(*anonymous*) = "ats_symenv.dats"

(* ****** ******* *)

#define THIS_FILE "ats_trans1_env.dats"

(* ****** ******* *)

typedef sym_t = $Sym.symbol_t
typedef symenv_t (itm:t@ype) = $SymEnv.symenv_t itm

(* ****** ******* *)

typedef e1xpenv = symenv_t (e1xp)

val the_e1xpenv = $SymEnv.symenv_make {e1xp} ()

implement the_e1xpenv_add (opr, e1xp) = let
(*
  val () = begin
    print "e1xp_add: opr = ";
    print opr;
    print_newline ()
  end
*)
in
  $SymEnv.symenv_insert (the_e1xpenv, opr, e1xp)
end // end of [the_e1xpenv_add]

implement the_e1xpenv_find (opr) = let
(*
  val () = begin
    print "e1xp_find: opr = ";
    print opr;
    print_newline ()
  end
*)
in
  $SymEnv.symenv_search (the_e1xpenv, opr)
end // end of [the_e1xpenv_find]

(* ****** ****** *)

typedef fxtyenv = symenv_t (fxty_t)

val the_fxtyenv = $SymEnv.symenv_make {fxty_t} ()

implement the_fxtyenv_add (opr, fxty) = let
  val () = case+
    $SymEnv.symenv_remove (the_fxtyenv, opr) of
    | ~Some_vt _ => () | ~None_vt () => ()
in
  $SymEnv.symenv_insert (the_fxtyenv, opr, fxty)
end // end of [the_fxtyenv_add]

implement the_fxtyenv_find (opr) = let
  val ans = $SymEnv.symenv_search (the_fxtyenv, opr)
in
  case+ ans of
  | ~None_vt () => begin
      $SymEnv.symenv_pervasive_search (the_fxtyenv, opr)
    end
  | Some_vt _ => (fold@ ans; ans)
end // end of [the_fxtyenv_find]

implement the_fxtyenv_pervasive_add_top () = let
  val m = $SymEnv.symenv_top (the_fxtyenv)
in
  $SymEnv.symenv_pervasive_add (the_fxtyenv, m)
end // end of [fxtyenv_pervasive_add_top]

(* ****** ****** *)

implement ats_fxtyenv_prerr () = let
  val r_m = $SymEnv.symenv_ref_top the_fxtyenv
  val kis = $SymEnv.symmap_ref_list (r_m)
  typedef ki = @(sym_t, fxty_t)
  fun loop {n:nat} .<n>.
    (kis: list_vt (ki, n)): void = begin case+ kis of
    | ~list_vt_cons (ki, kis) => let
        val (k, i) = ki; val () = begin
          $Sym.prerr_symbol_code k; prerr " = "; $Fix.prerr_fxty i;
          prerr_newline ()
        end // end of [val]
      in
        loop (kis)
      end
    | ~list_vt_nil () => ()
  end // end of [loop]
in
  loop kis
end // end of [ats_fxtyenv_prerr]

(* ****** ****** *)

local

assume trans1_level_token = unit_v
val the_trans1_level : ref int = ref_make_elt<int> 0

in // in of [local]

implement trans1_level_get () = !the_trans1_level

implement trans1_level_dec (pf | (*none*)) =
  let prval unit_v () = pf in
    !the_trans1_level := !the_trans1_level - 1
  end

implement trans1_level_inc () =
  let val () = !the_trans1_level := !the_trans1_level + 1 in
    (unit_v () | ())
  end

end // end of [local]

(* ****** ******* *)

implement trans1_env_pop () = begin
  $SymEnv.symenv_pop (the_e1xpenv);
  $SymEnv.symenv_pop (the_fxtyenv);
end

implement trans1_env_push () = begin
  $SymEnv.symenv_push (the_e1xpenv);
  $SymEnv.symenv_push (the_fxtyenv)
end

implement trans1_env_localjoin () = begin
  $SymEnv.symenv_localjoin (the_e1xpenv);
  $SymEnv.symenv_localjoin (the_fxtyenv)
end

implement trans1_env_save () = begin
  $SymEnv.symenv_save (the_e1xpenv);
  $SymEnv.symenv_save (the_fxtyenv)
end

implement trans1_env_restore () = begin
  $SymEnv.symenv_restore (the_e1xpenv);
  $SymEnv.symenv_restore (the_fxtyenv)
end

(* ****** ****** *)

staload HT = "ats_hashtbl.sats"
staload HASHTBL = "ats_hashtbl.dats"

local

val SIZE_HINT = 7
val theHashTable: $HT.hashtbl_t (string, d1eclst) =
  $HT.hashtbl_str_make_hint (SIZE_HINT)

in

implement staload_file_insert (fullname, d1cs) = let
  val ans = $HT.hashtbl_insert (theHashTable, fullname, d1cs)
in
  case+ ans of
  | ~Some_vt (d1c) => begin
      prerr "Internal Error: ";
      prerr THIS_FILE;
      prerr ": [staload_file_insert] failed.";
      prerr_newline ();
      exit {void} (1)
    end
  | ~None_vt () => ()
end // end of [staload_file_insert]

implement staload_file_search (fullname) =
  $HT.hashtbl_search (theHashTable, fullname)

end // end of [local]

(* ****** ****** *)

(* end of [ats_trans1_env.dats] *)
