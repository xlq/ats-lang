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

// Time: April 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Lst = "ats_list.sats"
staload Map = "ats_map_lin.sats"
staload Set = "ats_set_fun.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"
staload "ats_trans4.sats"
staload "ats_ccomp.sats"
staload "ats_ccomp_env.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

staload _(*anonymous*) = "ats_map_lin.dats"
staload _(*anonymous*) = "ats_set_fun.dats"

(* ****** ****** *)

local

val the_d2var_current_level = ref_make_elt<int> (0)

in // in of [local]

implement d2var_current_level_get () = begin
  !the_d2var_current_level
end

implement d2var_current_level_inc () = begin
  !the_d2var_current_level := !the_d2var_current_level + 1
end

implement d2var_current_level_inc_and_get () =
  let val n = !the_d2var_current_level; val n1 = n + 1 in
    !the_d2var_current_level := n1; n1
  end // end of [d2var_current_level_inc_and_get]

implement d2var_current_level_dec () = begin
  !the_d2var_current_level := !the_d2var_current_level - 1
end

implement d2var_current_level_dec_and_get () =
  let val n = !the_d2var_current_level; val n1 = n - 1 in
    !the_d2var_current_level := n1; n1
  end // end of [d2var_current_level_dec_and_get]

end // end of [local]

(* ****** ****** *)

extern fun compare_strlst_strlst (ss1: strlst, ss2: strlst):<> Sgn
overload compare with compare_strlst_strlst

implement compare_strlst_strlst (ss1, ss2) = begin
  case+ (ss1, ss2) of
  | (list_cons (s1, ss1), list_cons (s2, ss2)) => let
      val sgn = compare (s1, s2)
    in
      if sgn <> 0 then sgn else compare (ss1, ss2)
    end
  | (list_cons _, list_nil ()) =>  1
  | (list_nil (), list_cons _) => ~1
  | (list_nil (), list_nil ()) =>  0
end // end [compare_strlst_strlst]

extern fun compare_labstrlst_labstrlst
  (lss1: labstrlst, lss2: labstrlst):<> Sgn
overload compare with compare_labstrlst_labstrlst

implement compare_labstrlst_labstrlst
  (lss1, lss2) = begin case+ (lss1, lss2) of
  | (LABSTRLSTcons (l1, s1, lss1),
     LABSTRLSTcons (l2, s2, lss2)) => let
      val sgn = $Lab.compare_label_label (l1, l2)
    in
      if sgn <> 0 then sgn else let
        val sgn = compare_string_string (s1, s2)
      in
        if sgn <> 0 then sgn else compare (lss1, lss2)
      end
    end
  | (LABSTRLSTcons _, LABSTRLSTnil ()) =>  1
  | (LABSTRLSTnil (), LABSTRLSTnil ()) =>  0
  | (LABSTRLSTnil (), LABSTRLSTcons _) => ~1
end // end [compare_labstrlst_labstrlst]

extern fun compare_typkey_typkey (tk1: typkey, tk2: typkey):<> Sgn
overload compare with compare_typkey_typkey

implement compare_typkey_typkey (tk1, tk2) = begin
  case+ (tk1, tk2) of
  | (TYPKEYrec lss1, TYPKEYrec lss2) => compare (lss1, lss2)
  | (TYPKEYrec _, _) => ~1
  | (TYPKEYsum (i1, ss1), TYPKEYsum (i2, ss2)) =>
      let val sgn = compare (i1, i2) in
        if sgn <> 0 then sgn else compare (ss1, ss2)
      end
  | (TYPKEYsum _, TYPKEYrec _) =>  1
  | (TYPKEYsum _, TYPKEYuni _) => ~1
  | (TYPKEYuni lss1, TYPKEYuni lss2) => compare (lss1, lss2)
  | (TYPKEYuni _, _) =>  1
end // end of [compare_typkey_typkey]

(* ****** ****** *)

local

val the_typdef_base = ref_make_elt<string> ("ats_anairiats")
val the_typdef_count = ref_make_elt<int> (0)

in // in of [local]

extern fun typdef_base_get (): string
extern fun typdef_base_set (base: string): void

implement typdef_base_get () = !the_typdef_base
implement typdef_base_set (base) = !the_typdef_base := base

extern fun typdef_count_get_and_inc (): int

implement typdef_count_get_and_inc () = begin
  (!the_typdef_count := n+1; n) where { val n = !the_typdef_count }
end // end of [typdef_count_get]

end // end of [local]

(* ****** ****** *)

local

val the_typdeflst = ref_make_elt<typdeflst> (TYPDEFLSTnil ())

fn typdeflst_reverse
  (xs: typdeflst): typdeflst = let
  fun aux (xs: typdeflst, ys: typdeflst)
    : typdeflst = begin case+ xs of
    | TYPDEFLSTcons (_(*tk*), _(*name*), !xs1) => let
        val xs1_v = !xs1; val () = (!xs1 := ys; fold@ (xs))
      in
        aux (xs1_v, xs)
      end // end of [TYPDEFLSTcons]
    | ~TYPDEFLSTnil () => ys
  end // end of [aux]
in
  aux (xs, TYPDEFLSTnil ())
end // end of [typdeflst_reverse]

in

extern fun typdeflst_add (tk: typkey, name: string): void

implement typdeflst_add (tk, name) = let
  val (pfbox | p) = ref_get_view_ptr (the_typdeflst)
  prval vbox pf = pfbox
in
  !p := TYPDEFLSTcons (tk, name, !p)
end // end of [local]

implement typdeflst_get () = let
  val res = let
    val (pfbox | p) = ref_get_view_ptr (the_typdeflst)
    prval vbox pf = pfbox
    val res = !p
  in
    !p := TYPDEFLSTnil (); res
  end // end of [val]
in
  typdeflst_reverse (res)
end // end of [typdeflst_get]

end // end of [local]

(* ****** ****** *)

local

viewtypedef typdefmap = $Map.map_vt (typkey, string)

fn typdefmap_nil () = $Map.map_make (compare_typkey_typkey)
val the_typdefmap = ref_make_elt<typdefmap> (typdefmap_nil ())

in

(* ****** ****** *)

extern fun typdefmap_add_rec (tk: typkey): string
extern fun typdefmap_add_sum (tk: typkey): string
extern fun typdefmap_add_uni (tk: typkey): string

(* ****** ****** *)

implement typdefmap_add_rec (tk) = let
  val base = typdef_base_get ()
  val n = typdef_count_get_and_inc ()
  val name_rec = tostringf ("%s_rec_%i", @(base, n))
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_typdefmap)
    prval vbox pf = pfbox
  in
    $Map.map_insert (!p, tk, name_rec)
  end // end of [val]
in
  name_rec
end // end of [typdefmap_add_rec]

implement typdefmap_add_sum (tk) = let
  val base = typdef_base_get ()
  val n = typdef_count_get_and_inc ()
  val name_sum = tostringf ("%s_sum_%i", @(base, n))
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_typdefmap)
    prval vbox pf = pfbox
  in
    $Map.map_insert (!p, tk, name_sum)
  end // end of [val]
in
  name_sum
end // end of [typdefmap_add_sum]

implement typdefmap_add_uni (tk) = let
  val base = typdef_base_get ()
  val n = typdef_count_get_and_inc ()
  val name_uni = tostringf ("%s_uni_%i", @(base, n))
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_typdefmap)
    prval vbox pf = pfbox
  in
    $Map.map_insert (!p, tk, name_uni)
  end // end of [val]
in
  name_uni
end // end of [typdefmap_add_uni]

implement typdefmap_find (tk) = let
  val oname = let
    val (pfbox | p) = ref_get_view_ptr (the_typdefmap)
    prval vbox pf = pfbox
  in
    $Map.map_search (!p, tk)
  end // end of [val]
in
  case+ oname of
  | ~Some_vt name => name | ~None_vt () => let
      val name = (case+ tk of
        | TYPKEYrec _ => typdefmap_add_rec (tk)
        | TYPKEYsum _ => typdefmap_add_sum (tk)
        | TYPKEYuni _ => typdefmap_add_uni (tk)
      ) : string
      val () = typdeflst_add (tk, name)
    in
      name
    end
end // end of [typdefmap_find]

end // end of [local]

(* ****** ****** *)

local

val the_datcstlst = ref_make_elt<datcstlst> (DATCSTLSTnil ())

fn datcstlst_reverse
  (xs: datcstlst): datcstlst = let
  fun aux (xs: datcstlst, ys: datcstlst)
    : datcstlst = begin case+ xs of
    | DATCSTLSTcons (_, !xs1) => let
        val xs1_v = !xs1; val () = (!xs1 := ys; fold@ (xs))
      in
        aux (xs1_v, xs)
      end
    | ~DATCSTLSTnil () => ys
  end // end of [aux]
in
  aux (xs, DATCSTLSTnil ())
end // end of [datcstlst_reverse]

in

implement datcstlst_free (s2cs) = begin
  case+ s2cs of
  | ~DATCSTLSTcons (_, s2cs) => datcstlst_free s2cs
  | ~DATCSTLSTnil () => ()
end // end of [datcstlst_free]

implement the_datcstlst_add (s2c) = let
  val (pfbox | p) = ref_get_view_ptr (the_datcstlst)
  prval vbox pf = pfbox
in
 !p := DATCSTLSTcons (s2c, !p)
end // end of [the_datcstlst_add]

implement the_datcstlst_adds (s2cs) = begin
  case+ s2cs of
  | S2CSTLSTcons (s2c, s2cs) => begin
      the_datcstlst_add s2c; the_datcstlst_adds s2cs
    end
  | S2CSTLSTnil () => ()
end // end of [the_datcstlst_adds]

implement the_datcstlst_get () = let
  val s2cs = let
    val (pfbox | p) = ref_get_view_ptr (the_datcstlst)
    prval vbox pf = pfbox
    val s2cs = !p
  in
    !p := DATCSTLSTnil (); s2cs
  end
in
  datcstlst_reverse (s2cs)
end // end of [the_datcstlst_get]

end // end of [local]

(* ****** ****** *)

local

val the_exnconlst = ref_make_elt<exnconlst> (EXNCONLSTnil ())

fn exnconlst_reverse
  (xs: exnconlst): exnconlst = let
  fun aux (xs: exnconlst, ys: exnconlst)
    : exnconlst = begin case+ xs of
    | EXNCONLSTcons (_, !xs1) => let
        val xs1_v = !xs1; val () = (!xs1 := ys; fold@ (xs))
      in
        aux (xs1_v, xs)
      end
    | ~EXNCONLSTnil () => ys
  end // end of [aux]
in
  aux (xs, EXNCONLSTnil ())
end // end of [exnconlst_reverse]

in

implement exnconlst_free (d2cs) = begin
  case+ d2cs of
  | ~EXNCONLSTcons (_, d2cs) => exnconlst_free d2cs
  | ~EXNCONLSTnil () => ()
end // end of [exnconlst_free]

implement the_exnconlst_add (d2c) = let
  val (pfbox | p) = ref_get_view_ptr (the_exnconlst)
  prval vbox pf = pfbox
in
 !p := EXNCONLSTcons (d2c, !p)
end // end of [the_exnconlst_add]

implement the_exnconlst_adds (d2cs) = begin
  case+ d2cs of
  | D2CONLSTcons (d2c, d2cs) => begin
      the_exnconlst_add d2c; the_exnconlst_adds d2cs
    end
  | D2CONLSTnil () => ()
end // end of [the_exnconlst_adds]

implement the_exnconlst_get () = let
  val d2cs = let
    val (pfbox | p) = ref_get_view_ptr (the_exnconlst)
    prval vbox pf = pfbox
    val d2cs = !p
  in
    !p := EXNCONLSTnil (); d2cs
  end
in
  exnconlst_reverse (d2cs)
end // end of [the_exnconlst_get]

end // end of [local]

(* ****** ****** *)

local

viewtypedef vartypsetlst = List_vt (vartypset)

val the_vartypset = begin
  ref_make_elt<vartypset> ($Set.set_nil)
end

val the_vartypsetlst = begin
  ref_make_elt<vartypsetlst> (list_vt_nil ())
end

in // in of [local]

implement the_vartypset_pop () = let
  var err: int = 0
  val x0 = !the_vartypset
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_vartypsetlst)
    prval vbox pf = pfbox
  in
    case+ !p of
    | ~list_vt_cons (x, xs) => begin
        $effmask_ref (!the_vartypset := x); !p := (xs: vartypsetlst)
      end
    | list_vt_nil () => (fold@ (!p); err := 1)
  end
  val () = // error reporting
    if err > 0 then begin
      prerr "Internal Error: ats_ccomp_env: the_vartypset_pop";
      prerr_newline ();
      $Err.abort {void} ()
    end
in
  x0
end // end of [the_vartypset_pop]

implement the_vartypset_push () = let
  val vts = !the_vartypset
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_vartypsetlst)
    prval vbox pf = pfbox
  in
    !p := list_vt_cons (vts, !p);
  end
in
  !the_vartypset := $Set.set_nil
end // end of [the_vartypset_push]

implement the_vartypset_add (vtp) = let
  val _new = $Set.set_insert<vartyp_t>
    (!the_vartypset, vtp, compare_vartyp_vartyp)
in
  !the_vartypset := _new
end // end of [the_vartypset_add]

end // end of [local]

implement vartypset_d2varlst_make (vtps) = let
  viewtypedef d2varlst_vt = List_vt d2var_t
  var d2vs: d2varlst_vt = list_vt_nil ()
  viewdef V = d2varlst_vt @ d2vs; viewtypedef VT = ptr d2vs
  fn f (pf: !V | vtp: vartyp_t, env: !VT)
    :<> void = begin
    !env := list_vt_cons (vartyp_var_get vtp, !env)
  end
  val () = vartypset_foreach_main {V} {VT} (view@ d2vs | vtps, f, &d2vs)
in
  $Lst.list_vt_reverse (d2vs)
end // end of [vartypset_d2varlst_make]

//

implement vartypset_union (vtps1, vtps2) =
  $Set.set_union (vtps1, vtps2, compare_vartyp_vartyp)

//

implement vartypset_foreach_main (pf | vtps, f, env) =
  $Set.set_foreach_main (pf | vtps, f, env)

implement vartypset_foreach_cloptr (vtps, f) =
  $Set.set_foreach_cloptr (vtps, f)

//

implement print_vartypset (vtps) = let
  var i: int = 0
  fn f (pf: !int @ i | vtp: vartyp_t, p: !ptr i): void =
    let val i = !p; val () = !p := i + 1 in
      if i > 0 then print (", "); print_vartyp vtp
    end
  val () = begin
    vartypset_foreach_main {int @ i} {ptr i} (view@ i | vtps, f, &i)
  end
in
  // empty
end // end of [print_vartypset]

implement prerr_vartypset (vtps) = let
  var i: int = 0
  fn f (pf: !int @ i | vtp: vartyp_t, p: !ptr i): void =
    let val i = !p; val () = !p := i + 1 in
      if i > 0 then prerr (", "); prerr_vartyp vtp
    end
  val () = begin
    vartypset_foreach_main {int @ i} {ptr i} (view@ i | vtps, f, &i)
  end
in
  // empty
end // end of [prerr_vartypset]

(* ****** ****** *)

local

viewtypedef funlabsetlst = List_vt (funlabset)

val the_funlabset = ref_make_elt<funlabset> ($Set.set_nil)
val the_funlabsetlst = ref_make_elt<funlabsetlst> (list_vt_nil ())

in // in of [local]

implement the_funlabset_pop () = let
  var err: int = 0
  val x0 = !the_funlabset
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_funlabsetlst)
    prval vbox pf = pfbox
  in
    case+ !p of
    | ~list_vt_cons (x, xs) => begin
        $effmask_ref (!the_funlabset := x); !p := (xs: funlabsetlst)
      end
    | list_vt_nil () => (fold@ (!p); err := 1)
  end
  val () = // error reporting
    if err > 0 then begin
      prerr "Internal Error: ats_ccomp_env: the_funlabset_pop";
      prerr_newline ();
      $Err.abort {void} ()
    end
in
  x0
end // end of [the_funlabset_pop]

implement the_funlabset_push () = let
  val fls = !the_funlabset
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_funlabsetlst)
    prval vbox pf = pfbox
  in
    !p := list_vt_cons (fls, !p);
  end
in
  !the_funlabset := $Set.set_nil
end // end of [the_funlabset_push]

implement the_funlabset_add (fl) = let
  val _new = begin
    $Set.set_insert<funlab_t> (!the_funlabset, fl, compare_funlab_funlab)
  end
in
  !the_funlabset := _new
end // end of [the_funlabset_add]

implement the_funlabset_mem (fl) = begin
  $Set.set_member<funlab_t> (!the_funlabset, fl, compare_funlab_funlab)
end // end of [the_funlabset_mem]

implement funlabset_foreach_main
  (pf | fls, f, env) = $Set.set_foreach_main (pf | fls, f, env)

implement funlabset_foreach_cloptr
  (fls, f) = $Set.set_foreach_cloptr (fls, f)

end // end of [local]

(* ****** ****** *)

local

val the_dynconset = ref_make_elt<dynconset> ($Set.set_nil) 

in

implement the_dynconset_add (d2c) = let
  val _new = $Set.set_insert<d2con_t> (!the_dynconset, d2c, compare_d2con_d2con)
in
  !the_dynconset := _new
end // end of [the_dynconset_add]

implement the_dynconset_get () = !the_dynconset

implement dynconset_foreach_main (pf | d2cs, f, env) =
  $Set.set_foreach_main (pf | d2cs, f, env)

end // end of [local]

(* ****** ****** *)

local

val the_dyncstset = ref_make_elt<dyncstset> ($Set.set_nil) 

in

fn the_dyncstset_add (d2c: d2cst_t): void = let
  val hit0 = s2exp_tr (1(*deep*), d2cst_typ_get d2c)
  val hit0 = hityp_normalize hit0
  val () = d2cst_hityp_set (d2c, Some hit0)
  val _new = $Set.set_insert<d2cst_t> (!the_dyncstset, d2c, compare_d2cst_d2cst)
in
  !the_dyncstset := _new
end // end of [the_dyncstset_add]

implement the_dyncstset_add_if (d2c) = let
  val ismem = begin
    $Set.set_member<d2cst_t> (!the_dyncstset, d2c, compare_d2cst_d2cst)
  end
in
  if ismem then () (*already added*) else the_dyncstset_add (d2c)
end // end of [the_dyncstset_add_if]

implement the_dyncstset_get () = !the_dyncstset

implement dyncstset_foreach_main (pf | d2cs, f, env) =
  $Set.set_foreach_main (pf | d2cs, f, env)

end // end of [local]

(* ****** ****** *)

local

val the_extypelst = ref_make_elt<extypelst> (EXTYPELSTnil ())

in // in of [local]

implement the_extypelst_add (name, hit) = let
  val (pfbox | p) = ref_get_view_ptr (the_extypelst)
  prval vbox pf = pfbox
in
  !p := EXTYPELSTcons (name, hit, !p)
end // end of [the_extypelst_add]

implement the_extypelst_get () = let
  val (pfbox | p) = ref_get_view_ptr (the_extypelst)
  prval vbox pf = pfbox
  val res = !p; val () = !p := EXTYPELSTnil ()
in
  res
end // end of [the_extypelst_add]

end // end of [local]

(* ****** ****** *)

local

val the_extvallst = ref_make_elt<extvallst> (EXTVALLSTnil ())

fn extvallst_reverse
  (xs: extvallst): extvallst = let
  fun aux (xs: extvallst, ys: extvallst)
    : extvallst = begin case+ xs of
    | EXTVALLSTcons (_(*name*), _(*vp*), !xs1) => let
        val xs1_v = !xs1; val () = (!xs1 := ys; fold@ (xs))
      in
        aux (xs1_v, xs)
      end
    | ~EXTVALLSTnil () => ys
  end // end of [aux]
in
  aux (xs, EXTVALLSTnil ())
end // end of [extvallst_reverse]

in // in of [local]

implement the_extvallst_add (name, hit) = let
  val (pfbox | p) = ref_get_view_ptr (the_extvallst)
  prval vbox pf = pfbox
in
  !p := EXTVALLSTcons (name, hit, !p)
end // end of [the_extvallst_add]

implement the_extvallst_get () = let
  val res = let
    val (pfbox | p) = ref_get_view_ptr (the_extvallst)
    prval vbox pf = pfbox
    val res = !p
  in
    !p := EXTVALLSTnil (); res
  end
in
  extvallst_reverse (res)
end // end of [the_extvallst_get]

implement extvallst_free (exts) = begin case+ exts of
  | ~EXTVALLSTcons (_(*name*), _(*vp*), exts) => extvallst_free exts
  | ~EXTVALLSTnil () => ()
end // end of [extvallst_free]

end // end of [local]

(* ****** ****** *)

local

val the_extcodelst = ref_make_elt<extcodelst> (EXTCODELSTnil ())

fn extcodelst_reverse
  (xs: extcodelst): extcodelst = let
  fun aux (xs: extcodelst, ys: extcodelst)
    : extcodelst = begin case+ xs of
    | EXTCODELSTcons (_(*pos*), _(*code*), !xs1) => let
        val xs1_v = !xs1; val () = (!xs1 := ys; fold@ (xs))
      in
        aux (xs1_v, xs)
      end
    | ~EXTCODELSTnil () => ys
  end // end of [aux]
in
  aux (xs, EXTCODELSTnil ())
end // end of [extcodelst_reverse]

in // in of [local]

implement the_extcodelst_add (position, code) = let
  val (pfbox | p) = ref_get_view_ptr (the_extcodelst)
  prval vbox pf = pfbox
in
  !p := EXTCODELSTcons (position, code, !p)
end // end of [the_extcodelst_add]

implement the_extcodelst_get () = let
  val res = let
    val (pfbox | p) = ref_get_view_ptr (the_extcodelst)
    prval vbox pf = pfbox
    val res = !p
  in
    !p := EXTCODELSTnil (); res
  end
in
  extcodelst_reverse (res)
end // end of [the_extcodelst_get]

implement extcodelst_free (codes) = begin case+ codes of
  | ~EXTCODELSTcons (_, _, codes) => extcodelst_free (codes)
  | ~EXTCODELSTnil () => ()
end // end of [extcodelst_free]

end // end of [local]

(* ****** ****** *)

local

val the_stafilelst =
  ref_make_elt<stafilelst> (STAFILELSTnil ())

fn stafilelst_reverse
  (xs: stafilelst): stafilelst = let
  fun aux (xs: stafilelst, ys: stafilelst)
    : stafilelst = begin case+ xs of
    | STAFILELSTcons (_(*fil*), !xs1) => let
        val xs1_v = !xs1; val () = (!xs1 := ys; fold@ (xs))
      in
        aux (xs1_v, xs)
      end
    | ~STAFILELSTnil () => ys
  end // end of [aux]
in
  aux (xs, STAFILELSTnil ())
end // end of [stafilelst_reverse]

in // in of [local]

implement the_stafilelst_add (fil) = let
  val (pfbox | p) = ref_get_view_ptr (the_stafilelst)
  prval vbox pf = pfbox
in
  !p := STAFILELSTcons (fil, !p)
end // end of [the_stafilelst_add]

implement the_stafilelst_get () = let
  val (pfbox | p) = ref_get_view_ptr (the_stafilelst)
  prval vbox pf = pfbox
  val res = !p; val () = !p := STAFILELSTnil ()
in
  stafilelst_reverse (res)
end // end of [the_stafilelst_get]

implement stafilelst_free (fils) = begin
  case+ fils of
  | ~STAFILELSTcons (fil, fils) => stafilelst_free fils
  | ~STAFILELSTnil () => ()
end // end of [stafilelst_free]

end // end of [local]

(* ****** ****** *)

local

val the_dynfilelst =
  ref_make_elt<dynfilelst> (DYNFILELSTnil ())

in // in of [local]

implement the_dynfilelst_add (fil) = let
  val (pfbox | p) = ref_get_view_ptr (the_dynfilelst)
  prval vbox pf = pfbox
in
  !p := DYNFILELSTcons (fil, !p)
end // end of [the_dynfilelst_add]

implement the_dynfilelst_get () = let
  val (pfbox | p) = ref_get_view_ptr (the_dynfilelst)
  prval vbox pf = pfbox
  val res = !p; val () = !p := DYNFILELSTnil ()
in
  res
end // end of [the_dynfilelst_get]

implement dynfilelst_free (fils) = begin
  case+ fils of
  | ~DYNFILELSTcons (fil, fils) => dynfilelst_free fils
  | ~DYNFILELSTnil () => ()
end // end of [dynfilelst_free]

end // end of [local]

(* ****** ****** *)

local

assume funlab_token = unit_v
val the_funlablst = ref_make_elt<funlablst_vt> (list_vt_nil ())

in // in of [local]

implement funlab_pop (pf | (*none*)) = let
  prval unit_v () = pf
  var err: int = 0; val () = let
    val (vbox pf | p) = ref_get_view_ptr (the_funlablst)
  in
    case+ !p of
    | ~list_vt_cons (_, fls) => !p := (fls: funlablst_vt)
    | list_vt_nil () => (fold@ (!p); err := 1)
  end // end of [val]
in
  if err > 0 then begin
    prerr "Internal Error: ats_ccomp_env: funlab_pop"; prerr_newline ()
  end // end of [if]
end // end of [funlab_pop]

implement funlab_push (fl) = let
  val (vbox pf | p) = ref_get_view_ptr (the_funlablst)
  val () = !p := list_vt_cons (fl, !p)
in
  (unit_v () | ())
end // end of [funlab_push]

implement funlab_top () = let
  fn err (): funlab_t = begin
    prerr "Internal Error: ats_ccomp_env: [funlab_top]";
    prerr_newline ();
    $Err.abort {funlab_t} ()
  end
  val (vbox pf | p) = ref_get_view_ptr (the_funlablst)
in
  case+ !p of
  | list_vt_cons (fl, _) => begin
      fold@ (!p); fl
    end // end of [list_vt_cons]
  | list_vt_nil () => begin
      fold@ (!p); $effmask_ref (err ())
    end // end of [list_vt_nil]
end // end of [funlab_top]

end // end of [local]

(* ****** ****** *)

local

typedef funentry = '{
  funentry_loc= loc_t // location of the function in the source
, funentry_lab= funlab_t // the funentry label
, funentry_lev= int
, funentry_vtps= vartypset // local variables
, funentry_vtps_flag= int // 0/1: changeable/finalized
, funentry_labset= funlabset // list of funentrys called
, funentry_ret= tmpvar_t // storing the funentry return
, funentry_body= instrlst // instructions of the funentry body
, funentry_tailjoin= tailjoinlst // mutual tail-recursion
} // end of [funentry]

assume funentry_t = funentry

in

extern typedef "funentry_t" = funentry

fn _funentry_make (
    loc: loc_t
  , fl: funlab_t
  , level: int
  , fls: funlabset
  , vtps: vartypset
  , tmp_ret: tmpvar_t
  , inss: instrlst
  ) : funentry = '{
  funentry_loc= loc
, funentry_lab= fl
, funentry_lev= level
, funentry_vtps= vtps
, funentry_vtps_flag= 0 // needs finalized
, funentry_labset= fls
, funentry_ret= tmp_ret
, funentry_body= inss
, funentry_tailjoin= TAILJOINLSTnil ()
} // end of [_funentry_make]

implement funentry_make
   (loc, fl, level, vtps, fls, tmp_ret, inss) = begin
  _funentry_make (loc, fl, level, fls, vtps, tmp_ret, inss)
end // end of [funentry_make]

implement funentry_loc_get (entry) = entry.funentry_loc
implement funentry_lab_get (entry) = entry.funentry_lab
implement funentry_lev_get (entry) = entry.funentry_lev
implement funentry_vtps_get (entry) = entry.funentry_vtps
implement funentry_vtps_flag_get (entry) = entry.funentry_vtps_flag
implement funentry_labset_get (entry) = entry.funentry_labset
implement funentry_ret_get (entry) = entry.funentry_ret
implement funentry_body_get (entry) = entry.funentry_body
implement funentry_tailjoin_get (entry) = entry.funentry_tailjoin

end // end of [local]

implement funentry_associate (entry) =
  let val fl = funentry_lab_get (entry) in
    funlab_entry_set (fl, Some entry)
  end // end of [funentry_associate]

local

// transitive closure
fn funentry_labset_get_all
  (entry0: funentry_t): funlabset = let
  val level0 = funentry_lev_get (entry0)
  fun aux (fl: funlab_t):<cloptr1> void = let
    val entry = funlab_entry_get_some fl
    val level = funentry_lev_get (entry)
  in
    if level >= level0 then
      if ~(the_funlabset_mem fl) then let
        val () = the_funlabset_add (fl)
      in
        funlabset_foreach_cloptr (funentry_labset_get entry, aux)
      end // end of [if]
    else begin
      the_funlabset_add (fl)
    end // end of [if]
  end // end of [aux]
  val () = the_funlabset_push ()
  val fls0 = funentry_labset_get entry0
  val () = funlabset_foreach_cloptr (fls0, aux)
in
  the_funlabset_pop ()
end // end of [funentry_labset_get_all]

dataviewtype ENV (l:addr) = ENVcon (l) of (ptr l, int)

in

implement funentry_vtps_get_all (entry0) = let
  val vtps_flag = funentry_vtps_flag_get (entry0)
  var vtps_all: vartypset = funentry_vtps_get (entry0)
  viewdef V = vartypset @ vtps_all
  viewtypedef VT = ENV (vtps_all)
  fun aux
    (pf: !V | fl: funlab_t, env: !VT)
    : void = let
    val+ ENVcon (p, level0) = env
    val entry = funlab_entry_get_some (fl)
    val level = funentry_lev_get (entry)
    val vtps = (
      if level < level0 then begin
        // higher-level should be handled earlier
        funentry_vtps_get_all (entry)
      end else begin // [level = level0]
        funentry_vtps_get (entry)
      end // end of [if]
    ) : vartypset
    val () = begin
      !p := $Set.set_union (vtps, !p, compare_vartyp_vartyp)
    end
  in
    fold@ env
  end // end of [aux]
  val () =
    if vtps_flag = 0 then let
      val level0 = funentry_lev_get (entry0)
      val fls = funentry_labset_get_all (entry0)
      val env = ENVcon (&vtps_all, level0)
      val () = begin
        funlabset_foreach_main {V} {VT} (view@ vtps_all | fls, aux, env)
      end
      val+ ~ENVcon (_, _) = env
      val () = funentry_vtps_set (entry0, vtps_all)
      val () = funentry_vtps_flag_set (entry0)
    in
      // empty
    end
in
  vtps_all
end // end of [funentry_vtps_get_all]

end // end of [local]

(* ****** ****** *)

local

viewtypedef varindmap = $Map.map_vt (d2var_t, int)

dataviewtype ENV (l:addr, i:addr) = ENVcon (l, i) of (ptr l, ptr i)

fn varindmap_nil ():<> varindmap = begin
  $Map.map_make {d2var_t, int} (compare_d2var_d2var)
end

val the_varindmap = ref_make_elt<varindmap> (varindmap_nil ())

in

implement varindmap_find (d2v) = let
  val (pfbox | p) = ref_get_view_ptr (the_varindmap)
  prval vbox pf = pfbox
in
  $Map.map_search (!p, d2v)
end // end of [varindmap_find]

implement varindmap_find_some (d2v) = begin
  case+ varindmap_find d2v of
  | ~Some_vt ind => ind | ~None_vt () => begin
      prerr "Internal Error";
      prerr ": ats_ccomp_env: varindmap_find: d2v = ";
      prerr_d2var d2v;
      prerr_newline ();
      $Err.abort {int} ()
    end
end // end of [varindmap_find_some]

implement funentry_varindmap_reset () = let
  val (pfbox | p) = ref_get_view_ptr (the_varindmap)
  prval vbox pf = pfbox
  val () = $Map.map_free<d2var_t,int> (!p)
in
  !p := varindmap_nil ()
end // end of [funentry_varindmap_reset]

implement funentry_varindmap_set (vtps) = let
  var i: int = 0
  val [l:addr] (pfbox | r) = ref_get_view_ptr (the_varindmap)
  viewdef V = (varindmap @ l, int @ i)
  viewdef VT = ENV (l, i)
  fn f (pf: !V | vtp: vartyp_t, env: !VT):<> void = let
    prval @(pf_map, pf_int) = pf
    val+ ENVcon (p_l, p_i) = env
    val i = !p_i; val () = (!p_i := i + 1)
    val () = $Map.map_insert (!p_l, vartyp_var_get vtp, i)
  in
    pf := (pf_map, pf_int); fold@ env
  end
  prval vbox pf_map = pfbox
  prval pf = @(pf_map, view@ i)
  val env = ENVcon (r, &i)
  val () = vartypset_foreach_main {V} {VT} (pf | vtps, f, env)
  val+ ~ENVcon (_, _) = env
in
  pf_map := pf.0; view@ i := pf.1
end // end of [funentry_varindmap_set]

end // end of [local]

(* ****** ****** *)

local

val the_funlablst = begin
  ref_make_elt<funlablst_vt> (list_vt_nil ())
end

in // in of [local]

implement funentry_lablst_add (fl) = let
(*
  val () = begin
    prerr "funentry_lablst_add: fl = "; prerr fl; prerr_newline ()
  end
*)
  val (pfbox | p) = ref_get_view_ptr (the_funlablst)
  prval vbox pf = pfbox
in
  !p := list_vt_cons (fl, !p)
end // end of [funentry_lablst_add]

implement funentry_lablst_get () = let
  val res = let
    val (pfbox | p) = ref_get_view_ptr (the_funlablst)
    prval vbox pf = pfbox
    val res = !p
  in
    !p := list_vt_nil (); res
  end
in
  $Lst.list_vt_reverse (res)
end // end of [funentry_lablst_get]

end // end of [local]

(* ****** ****** *)

local

dataviewtype loopexnlablst =
  | LOOPEXNLABLSTcons of (tmplab_t, tmplab_t, loopexnlablst)
  | LOOPEXNLABLSTnil

val the_loopexnlablst =
  ref_make_elt<loopexnlablst> (LOOPEXNLABLSTnil ())

in

implement loopexnlablst_push (tl_brk, tl_cnt) = let
  val (pfbox | p) = ref_get_view_ptr (the_loopexnlablst)
  prval vbox pf = pfbox
in
  !p := LOOPEXNLABLSTcons (tl_brk, tl_cnt, !p)
end // end of [loopexnlablst_push]

implement loopexnlablst_pop () = let
  var err: int = 0
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_loopexnlablst)
    prval vbox pf = pfbox
  in
    case+ !p of
    | ~LOOPEXNLABLSTcons (_, _, tls) => (!p := tls)
    | LOOPEXNLABLSTnil () => (fold@ (!p); err := 1)
  end
in
  if err > 0 then begin
    prerr "Internal Error: ats_ccomp_env: loopexnlablst_pop";
    prerr_newline ();
    $Err.abort {void} ()
  end
end // end of [loopexnlablst_pop]

implement loopexnlablst_get (i) = let
  fn tmplab_gen (): tmplab_t = begin
    prerr "Internal Error: ats_ccomp_env: loopexnlablst_get";
    prerr_newline ();
    $Err.abort {tmplab_t} ()
  end
  val (pfbox | p) = ref_get_view_ptr (the_loopexnlablst)
  prval vbox pf = pfbox
in
  case+ !p of
  | LOOPEXNLABLSTcons (tl_brk, tl_cnt, _) =>
      (fold@ (!p); if i = 0 then tl_brk else tl_cnt)
  | LOOPEXNLABLSTnil () =>
      (fold@ (!p); $effmask_all (tmplab_gen ()))
end // end of [loopexnlablst_get]

end // end of [local]

(* ****** ****** *)

%{$

ats_void_type
ats_ccomp_env_funentry_vtps_set
  (ats_ptr_type entry, ats_ptr_type vtps) {
  ((funentry_t)entry)->atslab_funentry_vtps = vtps ; return ;
}

ats_void_type
ats_ccomp_env_funentry_vtps_flag_set (ats_ptr_type entry) {
  ((funentry_t)entry)->atslab_funentry_vtps_flag = 1 ; return ;
}

ats_void_type
ats_ccomp_env_funentry_tailjoin_set
  (ats_ptr_type entry, ats_ptr_type tjs) {
  ((funentry_t)entry)->atslab_funentry_tailjoin = tjs ; return ;
}

%}

(* ****** ****** *)

(* end of [ats_ccomp_env.dats] *)
