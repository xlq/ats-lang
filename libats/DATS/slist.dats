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
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
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
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)
//
(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // there is no need for dynloading at run-time

(* ****** ****** *)

staload "libats/SATS/slist.sats"

(* ****** ****** *)

implement
slseg_v_extend
  {a} (pfseg, pfnod) = let
  prfun extend
    {n:nat} {la,ly,lz:addr} .<n>. (
      pfseg: slseg_v (a, n, la, ly)
    , pfnod: node_v (a, ly, lz)
    ) :<prf> slseg_v (a, n+1, la, lz) =
    case+ pfseg of
    | slseg_v_cons (pf1nod, pf1seg) =>
        slseg_v_cons (pf1nod, slseg_v_extend (pf1seg, pfnod))
      // end of [slseg_v_cons]
    | slseg_v_nil () => slseg_v_cons (pfnod, slseg_v_nil ())
  // end of [extend]
in
  extend (pfseg, pfnod)
end // end of [slseg_v_extend]

(* ****** ****** *)

implement
slseg_v_append
  {a} (pf1seg, pf2seg) = let
  prfun append
    {n1,n2:nat}
    {la,lm,lz:addr} .<n1>. (
      pf1seg: slseg_v (a, n1, la, lm)
    , pf2seg: slseg_v (a, n2, lm, lz)
    ) :<prf> slseg_v (a, n1+n2, la, lz) = begin
    case+ pf1seg of
    | slseg_v_cons (pf1nod, pf1seg) =>
        slseg_v_cons (pf1nod, slseg_v_append (pf1seg, pf2seg))
      // end of [slseg_v_cons]
    | slseg_v_nil () => pf2seg
  end // end of [append]
in
  append (pf1seg, pf2seg)
end // end of [slseg_v_append]

(* ****** ****** *)

implement{a}
slist_free (xs) = let
  fun free {n:nat} {la:addr} .<n>. (
    pfseg: slist_v (a, n, la) | p: ptr la
  ) :<> void =
    if slist_is_cons (pfseg | p) then let
      prval slseg_v_cons (pfnod, pf1seg) = pfseg
      val p1 = node_get_next<a> (pfnod | p)
      val () = node_free<a> (pfnod | p)
    in
      free (pf1seg | p1)
    end else begin
      let prval slseg_v_nil () = pfseg in () end
    end // end of [if]
  // end of [free]
  prval (pfseg | p_xs) = slist_decode (xs)
in
  free (pfseg | p_xs)
end (* end of [slist_free] *)

(* ****** ****** *)

implement{a}
slist_append (xs, ys) = let
//
  fun loop {m,n:nat}
    {la1,lb1:addr} {la2:addr} .<m>. (
    pfnod: !node_v (a, la1, lb1) >> node_v (a, la1, lb1)
  , pf1lst: slist_v (a, m, lb1)
  , pf2lst: slist_v (a, n, la2)
  | p1: ptr la1, p2: ptr la2
  ) :<> #[lb1:addr] (
    slist_v (a, m+n, lb1) | void
  ) = let
    val p11 = node_get_next<a> (pfnod | p1)
  in
    if slist_is_cons (pf1lst | p11) then let
      prval slseg_v_cons (pf1nod, pf1lst1) = pf1lst
      val (pflst1 | ()) = loop (pf1nod, pf1lst1, pf2lst | p11, p2)
    in
      (slseg_v_cons (pf1nod, pflst1) | ())
    end else let
      prval slseg_v_nil () = pf1lst
      val () = node_set_next (pfnod | p1, p2)
    in
      (pf2lst | ())
    end (* end of [if] *)
  end // end of [loop]
//
  prval (pf1lst | p_xs) = slist_decode (xs)
  prval (pf2lst | p_ys) = slist_decode (ys)
//
in
  if slist_is_cons (pf1lst | p_xs) then let
    prval slseg_v_cons (pf1nod, pf1lst1) = pf1lst
    prval (pflst1 | ()) = loop (pf1nod, pf1lst1, pf2lst | p_xs, ys)
    prval () = slist_encode {a} (slseg_v_cons (pf1nod, pflst1) | xs)
  in
    xs
  end else let
    prval _ = xs
    prval slseg_v_nil () = pf1lst
    val () = slist_encode {a} (pf2lst | ys)
  in
    ys
  end (* end of [if] *)
end // end of [slist_append]

(* ****** ****** *)

implement{a}
slist_length (xs) = let
  fun loop
    {la:addr}
    {n,k:nat} .<n>. (
    pfseg: !slist_v (a, n, la)
  | p: !ptr la, k: size_t (k)
  ) :<> size_t (n+k) =
  if slist_is_cons (pfseg | p) then let
    prval slseg_v_cons (pfnod, pf1seg) = pfseg
    val p1 = node_get_next<a> (pfnod | p)
    val res = loop (pf1seg | p1, k + 1)
    prval () = pfseg := slseg_v_cons (pfnod, pf1seg)
  in
    res
  end else k // end of [if]
//
  prval (
    pfseg | p_xs
  ) = slist_decode (xs)
  val res = loop (pfseg | p_xs, 0)
  prval () = slist_encode (pfseg | xs)
//
in
  res
end // end of [slist_length]

(* ****** ****** *)

implement{a}
slist_foreach_funenv
  {v} {vt}
  (pfv | xs, f, env) = let
//
  fun loop {la,lz:addr} {n:nat} .<n>. (
    pfv: !v, pfseg: !slist_v (a, n, la)
  | p: !ptr la, f: (!v | &a, !vt) -<fun> void, env: !vt
  ) :<> void =
    if slist_is_cons (pfseg | p) then let
      prval slseg_v_cons (pfnod, pf1seg) = pfseg
      prval (pfat, fpfnod) = node_v_takeout1 {a} (pfnod)
      val () = f (pfv | !p, env)
      prval () = pfnod := fpfnod (pfat)
      val p1 = node_get_next (pfnod | p)
      val () = loop (pfv, pf1seg | p1, f, env)
    in
      pfseg := slseg_v_cons (pfnod, pf1seg)
    end // end of [if]
  (* end of [loop] *)
//
  prval (
    pfseg | p_xs
  ) = slist_decode (xs)
  val () = loop (pfv, pfseg | p_xs, f, env)
  prval () = slist_encode (pfseg | xs)
//
in
  // nothing
end // end of [slist_foreach_funenv]

(* ****** ****** *)

implement{a}
slist_foreach_clo
  {v} (pfv | xs, f) = let
//
  stavar l_f: addr
  val p_f: ptr l_f = &f
//
  typedef clo_t = (!v | &a) -<clo> void
  typedef vt = ptr l_f
  viewdef V = (v, clo_t @ l_f)
//
  fn app (
    pf: !V | x: &a, p_f: !vt
  ) :<> void = let
    prval pf1 = pf.1
    val () = !p_f (pf.0 | x)
    prval () = pf.1 := pf1
  in
    // nothing
  end // end of [app]
//
  prval pfV = (pfv, view@ f)
  val () = slist_foreach_funenv<a> {V} {vt} (pfV | xs, app, p_f)
  prval () = pfv := pfV.0
  prval () = view@ f := pfV.1
//
in
  // nothing
end // end of [slist_foreach_clo]
  
(* ****** ****** *)

(* end of [slist.dats] *)
