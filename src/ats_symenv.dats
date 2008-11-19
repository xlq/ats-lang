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

// Time: October 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload Sym = "ats_symbol.sats"
staload Map = "ats_map_lin.sats"

(* ****** ****** *)

staload "ats_symenv.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

#define THIS_FILE "ats_symenv.dats"

(* ****** ****** *)

typedef sym_t = $Sym.symbol_t

(* ****** ****** *)

viewtypedef symmap (itm:t@ype) = $Map.map_vt (sym_t, itm)
viewtypedef symmaplst (itm:t@ype) = [n:nat] list_vt (symmap itm, n)

typedef symenv (itm:t@ype) = '{
  map= ref (symmap itm)
, maplst= ref (symmaplst itm)
, savedlst= ref (List_vt @(symmap itm, symmaplst itm))
, pervasive= ref (symmaplst itm)
}

(* ****** ****** *)

assume symmap_t = symmap
assume symenv_t = symenv

(* ****** ****** *)

implement{itm} symmap_search (m, k) =
  $Map.map_search<sym_t,itm> (m, k)

implement{itm} symmap_ref_search (r_m, k) = let
  val (vbox pf_m | p_m) = ref_get_view_ptr r_m
in
  $Map.map_search<sym_t,itm> (!p_m, k)
end

implement{itm} symmap_list (m) = $Map.map_list_pre m

implement{itm} symmap_ref_list (r_m) = let
  val (vbox pf_m | p_m) = ref_get_view_ptr r_m
in
  $Map.map_list_pre (!p_m)
end // end of [symmap_ref_list]

(* ****** ****** *)

fn symmap_make {itm:t@ype} ():<> symmap itm =
  $Map.map_make {sym_t,itm} ($Sym.compare_symbol_symbol)

fn{itm:t@ype} symmap_free (m: symmap itm):<> void = $Map.map_free m

fun{itm:t@ype}
  symmaplst_free {n:nat} .<n>. (ms: list_vt (symmap itm, n)):<> void =
  case+ ms of
  | ~list_vt_cons (m, ms) => (symmap_free<itm> m; symmaplst_free<itm> ms)
  | ~list_vt_nil () => ()

implement symenv_make {itm} () = '{
  map= ref_make_elt (symmap_make {itm} ())
, maplst= ref_make_elt (list_vt_nil ())
, savedlst= ref_make_elt (list_vt_nil ())
, pervasive= ref_make_elt (list_vt_nil ())
} // end of [symenv_make]

(* ****** ****** *)

implement{itm} symenv_insert (env, k, i) = let
  val (vbox pf_m | p_m) = ref_get_view_ptr env.map
in
  $Map.map_insert (!p_m, k, i)
end // end of [symenv_insert]

implement{itm} symenv_remove (env, k) = let
  val (vbox pf_m | p_m) = ref_get_view_ptr env.map
in
  $Map.map_remove (!p_m, k)
end // end of [symenv_insert]

(* ****** ****** *)

fun{itm:t@ype} symmaplst_search {n:nat} .<n>.
  (ms0: !list_vt (symmap itm, n), k: sym_t):<> Option_vt itm =
  case+ ms0 of
  | list_vt_cons (!m, !ms) => let
      val ans = $Map.map_search (!m, k)
    in
      case+ ans of
      | Some_vt _ => (fold@ ms0; fold@ ans; ans)
      | ~None_vt () => let
          val ans = symmaplst_search<itm> (!ms, k)
        in
          fold@ ms0; ans
        end
    end
  | list_vt_nil () => (fold@ ms0; None_vt ())

implement{itm} symenv_search (env, k) = let
  val ans =
    let val (vbox pf_m | p_m) = ref_get_view_ptr env.map in
      $Map.map_search (!p_m, k)
    end
in
  case+ ans of
  | Some_vt _ => (fold@ ans; ans)
  | ~None_vt () => let
      val (vbox pf_ms | p_ms) = ref_get_view_ptr env.maplst
    in
      symmaplst_search<itm> (!p_ms, k)
    end
  
end // end of [symenv_search]

implement{itm} symenv_pervasive_search (env, k) = let
  val (vbox pf_ms | p_ms) = ref_get_view_ptr env.pervasive
in
  symmaplst_search<itm> (!p_ms, k)
end

(* ****** ****** *)

implement{itm} symenv_pop (env) = let
  fn abort (): symmap itm = begin
    prerr "Internal Error: "; prerr THIS_FILE;
    prerr ": [symenv_pop]: [env.maplst] is empty";
    prerr_newline ();
    exit (1)
  end // [abort]

  val m = (let
    val (vbox pf_ms | p_ms) = ref_get_view_ptr env.maplst
  in
    case+ !p_ms of
    | ~list_vt_cons (m, ms) => begin
        !p_ms := (ms: symmaplst itm); m
      end // end of [list_vt_cons]
    | list_vt_nil () => begin
        fold@ (!p_ms); $effmask_ref (abort ())
      end // end of [list_vt_nil]
  end) : symmap itm

  val (vbox pf_m | p_m) = ref_get_view_ptr env.map
in
  symmap_free<itm> (!p_m); !p_m := m
end // end of [symenv_pop]

//

implement symenv_push {itm} (env) = let
  val m = let
    val (vbox pf_m | p_m) = ref_get_view_ptr env.map
    val m = !p_m
  in
    !p_m := symmap_make (); m
  end : symmap itm

  val (vbox pf_ms | p_ms) = ref_get_view_ptr env.maplst
in
  !p_ms := list_vt_cons (m, !p_ms)
end // end of [symenv_push]

(* ****** ****** *)

implement symenv_save {itm} (env) = let
  val m = let
    val (vbox pf_m | p_m) = ref_get_view_ptr env.map
    val m = !p_m
  in
    !p_m := symmap_make (); m
  end : symmap itm

  val ms = let
    val (vbox pf_ms | p_ms) = ref_get_view_ptr env.maplst
    val ms = !p_ms
  in
    !p_ms := list_vt_nil (); ms
  end : symmaplst itm

  val (vbox pf_saved | p_saved) = ref_get_view_ptr env.savedlst
in
  !p_saved := list_vt_cons ( @(m, ms), !p_saved )
end // end of [symenv_save]

//

implement{itm} symenv_restore (env) = let
  viewtypedef mms = @(symmap itm, symmaplst itm)

  fn abort (): mms = begin
    prerr "Internal Error: "; prerr THIS_FILE;
    prerr ": [symenv_restore]: [env.savedlst] is empty";
    prerr_newline ();
    exit (1)
  end // end of [abort]

  val (m, ms) = let
    val (vbox pf_saved | p_saved) = ref_get_view_ptr env.savedlst
  in
    case+ !p_saved of
    | ~list_vt_cons (mms, rest) => begin
        !p_saved := (rest: List_vt mms); mms
      end
    | list_vt_nil () => begin
        fold@ (!p_saved); $effmask_ref (abort ())
      end
  end : mms

  val () = let
    val (vbox pf_m | p_m) = ref_get_view_ptr env.map
  in
    symmap_free<itm> (!p_m); !p_m := m
  end

  val () = let
    val (vbox pf_ms | p_ms) = ref_get_view_ptr env.maplst
  in
    symmaplst_free<itm> (!p_ms); !p_ms := ms
  end
in
  // no return value
end // end of [symenv_restore]

(* ****** ****** *)

implement symenv_top (env) = let
  val r_m = env.map
  val (vbox pf_m | p_m) = ref_get_view_ptr r_m
  val m = !p_m
in
  !p_m := symmap_make (); m
end // end of [symenv_top]

implement symenv_ref_top (env) = env.map

implement{itm} symenv_localjoin (env) = let
  fn abort (): symmap itm = begin
    prerr "Internal Error: "; prerr THIS_FILE;
    prerr ": [symenv_localjoin]: [env.maplst] is empty";
    prerr_newline ();
    exit (1)
  end // end of [symenv_localjoint]

  val m1 = m where {
    val (vbox pf_ms | p_ms) = ref_get_view_ptr env.maplst
    val m = (case+ !p_ms of
      | ~list_vt_cons (m, ms) => begin
          !p_ms := (ms: symmaplst itm); m
        end // list of [list_vt_cons]
      | list_vt_nil () => begin
          fold@ (!p_ms); $effmask_ref (abort ())
        end // end of [list_vt_nil]
    ) : symmap itm
  } // end of [where]

  val () = symmap_free<itm> m1

  val m2 = m where {
    val (vbox pf_ms | p_ms) = ref_get_view_ptr env.maplst
    val m = (case+ !p_ms of
      | ~list_vt_cons (m, ms) => (!p_ms := (ms: symmaplst itm); m)
      | list_vt_nil () => begin
          fold@ (!p_ms); $effmask_ref (abort ())
        end
    ) : symmap itm 
  } // end of [where]

  val (vbox pf_m | p_m) = ref_get_view_ptr env.map
in
  !p_m := $Map.map_join (m2, !p_m)
end // end of [symenv_localjoin]

(* ****** ****** *)

implement symenv_pervasive_add (env, m) = let
  val (vbox pf_ms | p_ms) = ref_get_view_ptr env.pervasive
in
  !p_ms := list_vt_cons (m, !p_ms)
end // end of [symenv_pervasive_add]

(* ****** ****** *)

(* end of [ats_symenv.dats] *)
