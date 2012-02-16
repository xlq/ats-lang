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
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
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

(*
**
** A functional map implementation based on ordered lists
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: May 18, 2011
**
*)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading at run-time

(* ****** ****** *)

staload
_(*anon*) = "prelude/DATS/list.dats"

(* ****** ****** *)

staload "libats/SATS/funmset_listord.sats"

(* ****** ****** *)
//
// a specialized version can be implemented on the spot
//
implement{elt} compare_elt_elt (x1, x2, cmp) = cmp (x1, x2)
//
(* ****** ****** *)

assume
mset_t0ype_type (elt: t@ype) = List @(Pos, elt)

(* ****** ****** *)

implement{} funmset_make_nil () = list_nil ()

implement{a} funmset_make_sing (x) = list_cons ((1, x), list_nil)

implement{a}
funmset_make_list
  (xs, cmp) = let
  var env: ptr = null
  var !p_clo = @lam (x1: &a, x2: &a): int =<clo> cmp (x1, x2)
  val xs = list_copy (xs)
  val xs = list_vt_mergesort (xs, !p_clo)
  fun ntimes {k:nat} .<k>. (
    xs: list_vt (a, k), x0: a, n: &Pos >> Pos
  ) :<> [k1:nat | k1 <= k] list_vt (a, k1) =
    case+ xs of
    | list_vt_cons (x, !p_xs) => let
        val sgn = compare_elt_elt (x0, x, cmp)
      in
        if sgn < 0 then let
          prval () = fold@ (xs) in xs
        end else let
          val () = n := n + 1
          val xs1 = !p_xs
          val () = free@ {a}{0} (xs)
        in
          ntimes (xs1, x0, n)
        end // end of [if]
      end // end of [list_vt_cons]
    | list_vt_nil () => let
        prval () = fold@ (xs) in xs
      end // end of [list_vt_nil]
  // end of [ntimes]
  fun loop {k:nat} .<k>. (
    xs: list_vt (a, k), res: &mset(a)? >> mset(a)
  ) :<> void =
    case+ xs of
    | ~list_vt_cons (x0, xs) => let
        var n: Pos = 1
        val xs = ntimes (xs, x0, n)
        val nx0 = @(n, x0)
        val () = res := list_cons {..}{0} (nx0, ?)
        val+ list_cons (_, !p_res) = res
        val () = loop (xs, !p_res)
        prval () = fold@ (res)
      in
        // nothing
      end // end of [list_vt_cons]
    | ~list_vt_nil () => let
        val () = res := list_nil () in (*nothing*)
      end // end of [list_vt_nil]
  // end of [loop]
  var res: mset(a)
  val () = loop (xs, res)
in
  res
end // end of [funmset_make_list]

(* ****** ****** *)

implement{a}
funmset_size (nxs) = let
  typedef nx = @(Pos, a)
  fun loop {k:nat} .<k>. (
    nxs: list (nx, k), res: size_t
  ) : size_t =
    case+ nxs of
    | list_cons (nx, nxs) => loop (nxs, res + nx.0)
    | list_nil () => res
  // end of [loop]
in
  loop (nxs, 0)
end // end of [funmset_size]

(* ****** ****** *)

implement{a}
funmset_get_ntime
  (nxs, x0, cmp) = let
  typedef nx = @(Pos, a)
  fun aux
    {k:nat} .<k>. (
    nxs: list (nx, k)
  ) :<cloref> Nat =
    case+ nxs of
    | list_cons (nx, nxs) => let
        val sgn = compare_elt_elt (x0, nx.1, cmp) in
        if sgn < 0 then 0 else (if sgn > 0 then aux (nxs) else nx.0)
      end // end of [list_cons]
    | list_nil () => 0
  // end of [aux]
  val n = aux (nxs)
in
  uint1_of_int1 (n)
end // end of [funmset_get_ntime]

(* ****** ****** *)

implement{a}
funmset_is_member
  (xs, x0, cmp) = funmset_get_ntime (xs, x0, cmp) > 0u
// end of [funmset_is_member]

implement{a}
funmset_isnot_member
  (xs, x0, cmp) = funmset_get_ntime (xs, x0, cmp) = 0u
// end of [funmset_isnot_member]

(* ****** ****** *)

implement{a}
funmset_listize (nxs) = let
  typedef nx = @(Pos, a)
  viewtypedef res = List_vt (a)
  fn* loop1 {k:nat} .<k,0>. (
    nxs: list (nx, k), res: &res? >> res
  ) :<> void =
    case+ nxs of
    | list_cons (nx, nxs) =>
        loop2 (nx.0, nx.1, nxs, res)
    | list_nil () => (res := list_vt_nil)
  (* end of [loop1] *)
  and loop2 {k,n:nat} .<k,n+1>. (
    n: int n, x: a, nxs: list (nx, k), res: &res? >> res
  ) :<> void =
    if n > 0 then let
      val () =
        res := list_vt_cons {..}{0} (x, ?)
      // end of [val]
      val list_vt_cons (_, !p_res) = res
      val () = loop2 (n-1, x, nxs, !p_res)
      prval () = fold@ (res)
    in
      // nothing
    end else
      loop1 (nxs, res)
    // end of [if]
  (* end of [loop2] *)
  var res: res // uninitialized
  val () = loop1 (nxs, res)
in
  res
end // end of [funmset_listize]
  
(* ****** ****** *)

(* end of [funmset_listord.dats] *)
