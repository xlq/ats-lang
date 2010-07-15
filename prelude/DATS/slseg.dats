(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // loaded by [ats_main_prelude]

(* ****** ****** *)

implement
slseg_v_extend
  {a} (pf_sl, pf_gc, pf_at) = let
  prfun extend {l1,l2,l3:addr} {n:nat} .<n>. (
      pf_sl: slseg_v (a, l1, l2, n)
    , pf_gc: free_gc_v (@(a, ptr), l2)
    , pf_at: (a, ptr l3) @ l2
    ) :<prf> slseg_v (a, l1, l3, n+1) = begin case+ pf_sl of
    | slseg_v_cons (pf1_gc, pf1_at, pf1_sl) => begin
        slseg_v_cons (pf1_gc, pf1_at, slseg_v_extend (pf1_sl, pf_gc, pf_at))
      end // end of [slseg_v_cons]
    | slseg_v_nil () => slseg_v_cons (pf_gc, pf_at, slseg_v_nil ())
  end // end of [extend]
in
  extend (pf_sl, pf_gc, pf_at)
end // end of [slseg_v_extend]

(* ****** ****** *)

implement
slseg_v_append
  {a} (pf1_sl, pf2_sl) = let
  prfun append {l1,l2,l3:addr} {n1,n2:nat} .<n1>. (
      pf1_sl: slseg_v (a, l1, l2, n1)
    , pf2_sl: slseg_v (a, l2, l3, n2)
    ) :<prf> slseg_v (a, l1, l3, n1+n2) = begin case+ pf1_sl of
    | slseg_v_cons (pf1_gc, pf1_at, pf1_sl) => begin
        slseg_v_cons (pf1_gc, pf1_at, slseg_v_append (pf1_sl, pf2_sl))
      end // end of [slseg_v_cons]
    | slseg_v_nil () => pf2_sl
  end // end of [append]
in
  append (pf1_sl, pf2_sl)
end // end of [slseg_v_append]

(* ****** ****** *)

implement{a}
slseg_free
  (pf_sl | p, n) = _free (pf_sl | p, n) where {
  typedef T = @(a, ptr)
  fun _free {l1,l2:addr} {n:nat} .<n>. (
      pf_sl: slseg_v (a, l1, l2, n) | p: ptr l1, n: int n
    ) :<> void =
    if n > 0 then let
      prval slseg_v_cons (pf_gc, pf_at, pf1_sl) = pf_sl
      val p1 = p->1; val () = ptr_free {T} (pf_gc, pf_at | p)
    in
      _free (pf1_sl | p1, n-1)
    end else begin
      let prval slseg_v_nil () = pf_sl in () end
    end // end of [if]
  // end of [_free]
} (* end of [slseg_free] *)

(* ****** ****** *)

implement{a}
slseg_length
  {l1,l2} {n} (pf_sl | p1, p2) = let
  fun loop
    {l1,l2:addr} {n,k:nat} .<n>. (
    pf_sl: !slseg_v (a, l1, l2, n)
  | p1: ptr l1, p2: ptr l2, k: size_t k
  ) :<> size_t (n+k) =
  if p1 <> p2 then let
    prval slseg_v_cons (pf_gc, pf_at, pf1_sl) = pf_sl
    val res = loop (pf1_sl | p1->1, p2, k+1)
    prval () = pf_sl := slseg_v_cons (pf_gc, pf_at, pf1_sl)
  in
    res
  end else let
    prval () = __assert () where {
      extern prfun __assert (): [n <= 0] void
    } // end of [prval]
  in
    k
  end // end of [if]
in
  loop (pf_sl | p1, p2, 0)
end // end of [slseg_length]

(* ****** ****** *)

implement{a}
slseg_foreach_main
  {v} {vt} {l1,l2} {n} (pf, pf_sl | p, n, f, env) = let
  fun loop {l1,l2:addr} {n:nat} .<n>. (
      pf: !v, pf_sl: !slseg_v (a, l1, l2, n)
    | p: ptr l1, n: int n, f: (!v | &a, !vt) -<fun> void, env: !vt
    ) :<> void =
  if n > 0 then let
    prval slseg_v_cons (pf_gc, pf_at, pf1_sl) = pf_sl
    val () = f (pf | p->0, env); val () = loop (pf, pf1_sl | p->1, n-1, f, env)
  in
    pf_sl := slseg_v_cons (pf_gc, pf_at, pf1_sl)
  end // end of [if]
in
  loop (pf, pf_sl | p, n, f, env)
end // end of [slseg_foreach_main]

implement{a}
slseg_foreach_clo
  {v} {l1,l2} {n} (pf, pf_sl | p, n, f) = let
  stavar l_f: addr
  val p_f: ptr l_f = &f
  typedef clo_t = (!v | &a) -<clo> void
  typedef vt = ptr l_f
  viewdef v1 = (v, clo_t @ l_f)
  fn app (pf1: !v1 | x: &a, p_f: !vt):<> void = let
    prval pf11 = pf1.1
    val () = !p_f (pf1.0 | x)
    prval () = pf1.1 := pf11
  in
    // nothing
  end // end of [app]
  val pf1 = (pf, view@ f)
  val () = slseg_foreach_main<a> {v1} {vt} (pf1, pf_sl | p, n, app, p_f)
  prval () = pf := pf1.0
  prval () = view@ f := pf1.1
in
  // nothing
end // end of [slseg_foreach_clo]
  
(* ****** ****** *)

// [slseg.sats] is already loaded by a call to [pervasive_load]
staload _(*anonymous*) = "prelude/SATS/slseg.sats" // this forces that the static
// loading function for [slseg.sats] is to be called at run-time
// this is really needed only if some datatypes are declared in [slseg.sats]

(* ****** ****** *)

(* end of [slseg.dats] *)
