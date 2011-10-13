(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
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
//
// Author: Artyom Shalkhakov (artyom.shalkhakov AT gmail DOT com)
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0 // there is no need for staloading at run-time
#define ATS_DYNLOADFLAG 0 // there is no need for dynloading at run-time

(* ****** ****** *)

staload "libats/ngc/SATS/dlist.sats"

(* ****** ****** *)

extern castfn p2p {l:addr} (p: !ptr l):<> ptr l

(* ****** ****** *)

#define dcons dlseg_v_cons
#define dnil dlseg_v_nil
#define rcons rdlseg_v_cons
#define rnil rdlseg_v_nil

(* ****** ****** *)

extern
fun dlseg_ptr_is_cons
  {a:vt0p} {n:nat} {lf,lfp,lr,lrn:addr} (
  pf: !dlseg_v (a, n, lf, lfp, lr, lrn) | p: ptr lf
) :<> bool (n > 0) = "atspre_ptr_isnot_null"

extern
fun rdlseg_ptr_is_cons
  {a:vt0p} {n:nat} {lf,lfp,lr,lrn:addr} (
  pf: !rdlseg_v (a, n, lf, lfp, lr, lrn) | p: ptr lr
) :<> bool (n > 0) = "atspre_ptr_isnot_null"

(* ****** ****** *)

implement{a}
dlist_is_at_end {nf,nr} (xs) = let
  val (pf | ()) = dlist_unfold {a} (xs)
  stavar lm:addr
  prval pf = pf: dlist_v (a, nf, nr, lm)
  val p_xs = p2p (xs)
  prval dlist_v_cons (pf1dl, dlseg_v_cons (pfhd, pf2dl)) = pf
  val nx = dlnode_get_next<a> (pfhd | p_xs)
  var res: bool // uninitialized
in
  if :(pf: dlist_v (a, nf, nr, lm), res: bool (nr <= 1)) =>
    dlseg_ptr_is_cons {a} (pf2dl | nx) then let
    prval dlseg_v_cons (pf_at, pf21dl) = pf2dl
  in
    pf := dlist_v_cons (pf1dl, dlseg_v_cons (pfhd, dlseg_v_cons (pf_at, pf21dl)));
    res := false
  end else let
    prval dlseg_v_nil () = pf2dl
  in
    pf := dlist_v_cons (pf1dl, dlseg_v_cons (pfhd, dlseg_v_nil ()));
    res := true
  end; // end of [if]
  dlist_fold (pf | xs); // HX: no-op at run-time
  res
end // end of [dlist_is_at_end]

implement{a}
dlist_isnot_at_end (xs) = ~dlist_is_at_end<a> (xs)

implement{a}
dlist_is_at_beg {nf,nr} (xs) = let
  val (pf | ()) = dlist_unfold (xs)
  stavar lm:addr
  prval pf = pf: dlist_v (a, nf, nr, lm)
  val p_xs = p2p (xs)
  prval dlist_v_cons (pf1dl, dlseg_v_cons (pfhd, pf2dl)) = pf
  val pr = dlnode_get_prev<a> (pfhd | p_xs)
  var res: bool // uninitialized
in
  if :(pf: dlist_v (a, nf, nr, lm), res: bool (nf == 0)) =>
    rdlseg_ptr_is_cons {a} (pf1dl | pr) then let
    prval rdlseg_v_cons (pf11dl, pf_at) = pf1dl
  in
    pf := dlist_v_cons (rdlseg_v_cons (pf11dl, pf_at), dlseg_v_cons (pfhd, pf2dl));
    res := false
  end else let
    prval rdlseg_v_nil () = pf1dl
  in
    pf := dlist_v_cons (rdlseg_v_nil (), dlseg_v_cons (pfhd, pf2dl));
    res := true
  end; // end of [if]
  dlist_fold (pf | xs); // HX: no-op at run-time
  res
end // end of [dlist_is_at_beg]

implement{a} dlist_isnot_at_beg {nf,nr} (xs) = ~dlist_is_at_beg<a> (xs)

(* ****** ****** *)

implement{a}
dlist_nil () = dlist_encode (dlist_v_nil () | null)

implement{a}
dlist_sing {l,lp,ln} (
  pfnod
| p
) = (
  dlnode_set_next<a> (pfnod | p, null);
  dlnode_set_prev<a> (pfnod | p, null);
  dlist_encode (dlist_v_cons (rnil (), dcons (pfnod, dnil ())) | p)
) // end of [dlist_sing]

(* ****** ****** *)

implement{a}
dlist_insert_after
  {nf,nr} {l1,lp,ln}
  (pfnod | p1, xs) = let
  prval (pfdl | p2) = dlist_unfold {a} (xs)
  val p2 = xs // HX: this is optimized away
  prval dlist_v_cons (pf1dl, dlseg_v_cons (pfhd, pf2dl)) = pfdl
  val () = dlnode_set_prev<a> (pfnod | p1, p2)
  val nx = dlnode_get_next<a> (pfhd | p2)
  val () = dlnode_set_next<a> (pfnod | p1, nx)
  val () = dlnode_set_next<a> (pfhd | p2, p1)
in
  if nx > null then let
    prval dcons (pf_at, pf21dl) = pf2dl
    val () = dlnode_set_prev<a> (pf_at | nx, p1)
    prval () = pf2dl := dlseg_v_cons {a} (pf_at, pf21dl)
    prval () = pfdl := dlist_v_cons (pf1dl, dcons (pfhd, dcons (pfnod, pf2dl)))
    prval () = dlist_fold (pfdl | xs)
  in
    // nothing
  end else let
    prval () = __assert () where {
      extern prfun __assert (): [nr <= 0] void
    } // end of [prval]
    prval dnil () = pf2dl
    prval () = pf2dl := dnil {a} ()
    prval () = pfdl := dlist_v_cons (pf1dl, dcons (pfhd, dcons (pfnod, pf2dl)))
    prval () = dlist_fold (pfdl | xs)
  in
    // nothing
  end (* end of [if] *)
end // end of [dlist_insert_after]

implement{a}
dlist_insert_before
  {nf,nr} {l1,lp,ln}
  (pfnod | p1, xs) = let
  prval (pfdl | void) = dlist_unfold {a} (xs)
  val p2 = xs // HX: this is optimized away
  prval dlist_v_cons (pf1dl, dcons (pfhd, pf2dl)) = pfdl
  val () = dlnode_set_next<a> (pfnod | p1, p2)
  val pr = dlnode_get_prev<a> (pfhd | p2)
  val () = dlnode_set_prev<a> (pfhd | p2, p1)
  val () = dlnode_set_prev<a> (pfnod | p1, pr)
in
  if pr > null then let
    prval rcons (pf11dl, pf_at) = pf1dl
    val () = dlnode_set_next<a> (pf_at | pr, p1)
    prval () = pf1dl := rcons {a} (rcons {a} (pf11dl, pf_at), pfnod)
    prval () = pfdl := dlist_v_cons (pf1dl, dcons {a} (pfhd, pf2dl))
    prval () = dlist_fold (pfdl | xs)
  in
    // nothing
  end else let
    prval () = __assert () where {
      extern prfun __assert (): [nf <= 0] void
    } // end of [where]
    prval rdlseg_v_nil () = pf1dl
    prval () = pf1dl := rdlseg_v_cons {a} (rdlseg_v_nil {a} (), pfnod)
    prval () = pfdl := dlist_v_cons (pf1dl, dlseg_v_cons {a} (pfhd, pf2dl))
    prval () = dlist_fold (pfdl | xs)
  in
    // nothing
  end (* end of [if] *)
end // end of [dlist_insert_before]

implement{a}
dlist_remove {nf,nr} (xs) = let
  val (pfdl | p1) = dlist_decode {a} (xs) // casting
  prval dlist_v_cons (pf1dl, dlseg_v_cons (pfhd, pf2dl)) = pfdl
  val pr = dlnode_get_prev<a> (pfhd | p1)
  val nx = dlnode_get_next<a> (pfhd | p1)
  viewtypedef R = [nf',nr':nat | nf'+nr' == nf+nr-1] dlist (a, nf', nr')
in
  if :(xs: R) => nx > null then let
    prval dcons (pf2_at, pf21dl) = pf2dl
  in
    if :(xs: R) => pr > null then let
      prval rcons (pf11dl, pf1_at) = pf1dl
      val () = dlnode_set_next<a> (pf1_at | pr, nx)
      val () = dlnode_set_prev<a> (pf2_at | nx, pr)
      prval () = pfdl := dlist_v_cons (rcons {a} (pf11dl, pf1_at), dcons {a} (pf2_at, pf21dl))
    in
      xs := dlist_encode (pfdl | nx);      
    end else let      
      prval () = __assert () where {
        extern prfun __assert (): [nf <= 0] void
      } // end of [where]
      prval rnil () = pf1dl
      val () = dlnode_set_prev<a> (pf2_at | nx, null)
      prval () = pfdl := dlist_v_cons (rnil {a} (), dcons {a} (pf2_at, pf21dl))
    in
      xs := dlist_encode (pfdl | nx);
    end
  end else let
      prval () = __assert () where {
        extern prfun __assert (): [nr <= 1] void
      } // end of [where]
    prval dnil () = pf2dl
  in
    if :(xs: R) => pr > null then let
      prval rdlseg_v_cons (pf11dl, pf1_at) = pf1dl
      val () = dlnode_set_next<a> (pf1_at | pr, null)
      prval () = pfdl := dlist_v_cons (pf11dl, dcons {a} (pf1_at, dnil {a} ()))
    in
      xs := dlist_encode (pfdl | pr);
    end else let
      prval () = __assert () where {
        extern prfun __assert (): [nf <= 0] void
      } // end of [where]
      prval rdlseg_v_nil () = pf1dl
      prval () = pfdl := dlist_v_nil ()
    in
      xs := dlist_encode (pfdl | null)
    end
  end; // end of [if]
  (pfhd | p1)
end // end of [dlist_remove]

(* ****** ****** *)

implement{a}
dlist_free {nf,nr} (xs) = let
  fun loop0
    {n:nat} {lf,lmp,lm:addr} .<n>. (
    pf: rdlseg_v (a, n, lf, null, lmp, lm)
  | p: ptr lmp
  ) :<> void =
    if rdlseg_ptr_is_cons (pf | p) then let
      prval rcons (pf1, pfnod) = pf
      val p1 = dlnode_get_prev<a> (pfnod | p)
      val () = dlnode_free<a> (pfnod | p)
    in
      loop0 (pf1 | p1)
    end else begin
      let prval rnil () = pf in () end
    end // end of [loop0]
  fun loop1
    {n:nat} {l,lp,lr:addr} .<n>. (
    pf: dlseg_v (a, n, l, lp, lr, null)
  | p: ptr l
  ) :<> void =
    if dlseg_ptr_is_cons (pf | p) then let
      prval dcons (pfnod, pf1) = pf
      val p1 = dlnode_get_next<a> (pfnod | p)
      val () = dlnode_free<a> (pfnod | p)
    in
      loop1 (pf1 | p1)
    end else begin
      let prval dnil () = pf in () end
    end // end of [loop1]
in
  if dlist_is_cons (xs) then let
    val (pf | p) = dlist_decode {a} (xs) // casting
    prval dlist_v_cons (pf1, dcons (pfhd, pf2)) = pf
    val pr = dlnode_get_prev<a> (pfhd | p)
    val nx = dlnode_get_next<a> (pfhd | p)
    val () = dlnode_free<a> (pfhd | p)
  in
    loop0 (pf1 | pr);
    loop1 (pf2 | nx)
  end else let
    val (pf | p) = dlist_decode {a} (xs) // casting
    prval dlist_v_nil () = pf
  in
    (*empty*)
  end // end of [if]
end // end of [dlist_free]

implement{a}
dlist_free_funenv
  {v} {vt} {nf,nr} (pfv | xs, f, env) = let
  fun loop0 {n:nat} {lf,lmp,lm:addr} .<n>. (
    pfv: !v, pf: rdlseg_v (a, n, lf, null, lmp, lm)
  | p: ptr lmp, f: (!v | &a >> a?, !vt) -<fun> void, env: !vt
  ) :<> void =
    if rdlseg_ptr_is_cons (pf | p) then let
      prval rcons (pf1, pfnod) = pf
      prval (pfat, fpfnod) = dlnode_v_takeout_val {a} (pfnod)
      val () = f (pfv | !p, env)
      prval () = pfnod := fpfnod {a?} (pfat)
      val p1 = dlnode_get_prev<a?> (pfnod | p)
      val () = dlnode_free<a> (pfnod | p)
    in
      loop0 (pfv, pf1 | p1, f, env)
    end else begin
      let prval rnil () = pf in () end
    end // end of [loop0]
  fun loop1 {n:nat} {l,lp,lr:addr} .<n>. (
    pfv: !v, pf: dlseg_v (a, n, l, lp, lr, null)
  | p: ptr l, f: (!v | &a >> a?, !vt) -<fun> void, env: !vt
  ) :<> void =
    if dlseg_ptr_is_cons (pf | p) then let
      prval dcons (pfnod, pf1) = pf
      prval (pfat, fpfnod) = dlnode_v_takeout_val {a} (pfnod)
      val () = f (pfv | !p, env)
      prval () = pfnod := fpfnod {a?} (pfat)
      val p1 = dlnode_get_next<a?> (pfnod | p)
      val () = dlnode_free<a> (pfnod | p)
    in
      loop1 (pfv, pf1 | p1, f, env)
    end else begin
      let prval dnil () = pf in () end
    end // end of [loop1]
in
  if dlist_is_cons xs then let
    val (pf | p) = dlist_decode {a} (xs) // casting
    prval dlist_v_cons (pf1, dcons (pfhd, pf2)) = pf
    val pr = dlnode_get_prev<a> (pfhd | p)
    val nx = dlnode_get_next<a> (pfhd | p)
    prval (pfat, fpfhd) = dlnode_v_takeout_val {a} (pfhd)
    val () = f (pfv | !p, env)
    prval () = pfhd := fpfhd {a?} (pfat)
    val () = dlnode_free<a> (pfhd | p)
  in
    loop0 (pfv, pf1 | pr, f, env);
    loop1 (pfv, pf2 | nx, f, env)
  end else let
    val (pf | p) = dlist_decode {a} (xs) // casting
    prval dlist_v_nil () = pf
  in
    (*empty*)
  end // end of [if]
end // end of [dlist_free_funenv]

implement{a}
dlist_free_fun
  (xs, f) = let
  val f = coerce (f) where {
    extern castfn coerce
      (f: (&a >> a?) -<fun> void):<> (!unit_v | &a >> a?, !ptr) -<fun> void
  } // end of [where]
  prval pf = unit_v ()
  val () = dlist_free_funenv<a> {..} {ptr} (pf | xs, f, null)
  prval unit_v () = pf
in
  ()
end // end of [dlist_free_fun]

implement{a}
dlist_free_vclo {v}
  (pf1 | xs, f) = let
  viewtypedef clo_t = (!v | &a >> a?) -<clo> void
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  prval pf = (pf1, view@ f)
  fn app (pf: !V | x: &a >> a?, p_f: !ptr l_f):<> void = let
    prval (pf1, pf2) = pf
    val () = !p_f (pf1 | x)
    prval () = pf := (pf1, pf2)
  in
    // nothing
  end // end of [app]
  val () = dlist_free_funenv<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = pf1 := pf.0
  prval () = view@ f := pf.1
in
  ()
end // end of [dlist_free_vclo]

(* ****** ****** *)

implement{a}
dlist_move_forward {nf,nr} (xs) = let
  val (pf | p1) = dlist_decode {a} (xs) // casting
  prval dlist_v_cons (pf1dl, dlseg_v_cons (pfhd, pf2dl)) = pf
  val res = dlnode_get_next<a> (pfhd | p1)
  prval () = pf := dlist_v_cons (rdlseg_v_cons (pf1dl, pfhd), pf2dl)
in
  xs := dlist_encode (pf | res)
end // end of [dlist_move_forward]

implement{a}
dlist_move_backward {nf,nr} (xs) = let
  val (pf | p1) = dlist_decode {a} (xs) // casting
  prval dlist_v_cons (
    rdlseg_v_cons (pf1dl, pf1), dlseg_v_cons (pfhd, pf2dl)
  ) = pf
  val res = dlnode_get_prev<a> (pfhd | p1)
  prval () = pf := dlist_v_cons (pf1dl, dlseg_v_cons (pf1, dlseg_v_cons (pfhd, pf2dl)))
in
  xs := dlist_encode (pf | res)
end // end of [dlist_move_backward]

(* ****** ****** *)

(* end of [dlist.dats] *)
