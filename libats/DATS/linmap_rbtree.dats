(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
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
** A map implementation based on AVL trees
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: September, 2011
**
*)

(* ****** ****** *)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading at run-time

(* ****** ****** *)

staload "libats/SATS/linmap_rbtree.sats"

(* ****** ****** *)

//
// a specialized version can be implemented on the spot
//
implement{key} compare_key_key (x1, x2, cmp) = cmp (x1, x2)

(* ****** ****** *)

#define BLK 0; #define RED 1
sortdef clr = {c:nat | c <= 1}
typedef color (c:int) = int c
typedef color = [c:clr] color c

(* ****** ****** *)

dataviewtype rbtree (
  key:t@ype, itm: viewt@ype
, int(*color*), int(*blackheight*), int(*violation*)
) =
  | E (key, itm, BLK, 0, 0)
  | {c,cl,cr:clr} {bh:nat} {v:int}
      {c == BLK && v == 0 || c == RED && v == cl+cr}
    T (key, itm, c, bh+1-c, v) of (
      color c, key, itm, rbtree0 (key, itm, cl, bh), rbtree0 (key, itm, cr, bh)
    ) // end of [T]
// rbtree0: for trees of no violations

where rbtree0
  (key:t@ype, itm:viewt@ype, c:int, bh:int) = rbtree (key, itm, c, bh, 0(*vio*))
// end of [rbtree0]

(* ****** ****** *)

assume map_t0ype_viewt0ype
  (key:t@ype, itm:viewt@ype) = [c:clr;bh:nat] rbtree0 (key, itm, c, bh)
// end of [assume]

(* ****** ****** *)

implement{} linmap_make_nil () = E ()

(* ****** ****** *)

implement{}
linmap_is_nil (t) =
  case+ t of | T _ => (fold@ t; false) | E () => (fold@ t; true)
// end of [linmap_is_nil]

implement{}
linmap_isnot_nil (t) =
  case+ t of | T _ => (fold@ t; true) | E () => (fold@ t; false)
// end of [linmap_isnot_nil]

(* ****** ****** *)

implement{key,itm}
linmap_size (t) = sz (t) where {
  fun sz
    {c:clr} {bh:nat} {v:nat} .<bh,c+v>.
    (t: !rbtree (key, itm, c, bh, v)):<> Nat =
    case+ t of
    | T (_(*c*), _(*key*), _(*itm*), !ptl, !ptr) => let
       val sz = 1 + sz (!ptl) + sz (!ptr) in (fold@ t; sz)
      end // end of [B]
    | E () => (fold@ t; 0)
  // end of [sz]
} // end of [linmap_size]

(* ****** ****** *)

implement{key,itm}
linmap_height (t) = ht (t) where {
  fun ht
    {c:clr} {bh:nat} {v:nat} .<bh,c+v>.
    (t: !rbtree (key, itm, c, bh, v)):<> Nat =
    case+ t of
    | T (_(*c*), _(*key*), _(*itm*), !ptl, !ptr) => let
       val ht = 1 + max (ht (!ptl), ht (!ptr)) in (fold@ t; ht)
      end // end of [B]
    | E () => (fold@ t; 0)
  // end of [ht]
} // end of [linmap_height]

(* ****** ****** *)
//
// HX: unsafe but convenient to implement
//
extern
fun{key:t0p;itm:vt0p}
linmap_takeout_ptr {l_res:addr} (
  m: &map (key, itm), k0: key, cmp: cmp key, res: ptr l_res
) :<> bool
// end of [linmap_takeout]

(* ****** ****** *)

implement{key,itm}
linmap_takeout
  (m, k0, cmp, res) = ans where {
  val ans = linmap_takeout_ptr<key,itm> (m, k0, cmp, &res)
  val [b:bool] ans = bool1_of_bool (ans)
  prval pf = __assert (view@ res) where {
    extern prfun __assert {l_res:addr} (pf: itm? @ l_res):<> opt (itm, b) @ l_res
  } // end of [prval]
  prval () = view@ res := pf
} // end of [linmap_takeout]

implement{key,itm}
linmap_remove (m, k0, cmp) = linmap_takeout_ptr<key,itm> (m, k0, cmp, null)

(* ****** ****** *)

(*
fun{key,itm:t@ype}
linmap_foreach_funenv {v:view} {vt:viewtype}
  (pf: !v | m: map (key, itm), f: (!v | key, itm, !vt) -<clo> void, env: !vt):<> void
// end of [linmap_foreach_funenv]
*)

implement{key,itm}
linmap_foreach_funenv {v} {vt}
  (pf | m, f, env) = foreach (pf | m, env) where {
  fun foreach {c:clr} {bh:nat} .<bh,c>.
    (pf: !v | t: !rbtree0 (key, itm, c, bh), env: !vt):<cloref> void =
    case+ t of
    | T (_(*c*), !p_k, !p_x, !p_tl, !p_tr) => begin
        foreach (pf | !p_tl, env); f (pf | !p_k, !p_x, env); foreach (pf | !p_tr, env); fold@ (t)
      end // end of [B]
    | E () => fold@ (t)
  // end of [foreach]
} // end of [linmap_foreach_funenv]

implement{key,itm}
linmap_foreach_fun
  (m, f) = let
//
  val f = coerce (f) where {
    extern castfn coerce
      (f: (key, &itm) -<fun> void):<> (!unit_v | key, &itm, !ptr) -<fun> void
  } // end of [val]
//
  prval pfu = unit_v ()
  val () = linmap_foreach_funenv<key,itm> {unit_v} {ptr} (pfu | m, f, null)
  prval unit_v () = pfu
//  
in
  // nothing
end // end of [linmap_foreach_fun]

(* ****** ****** *)

implement{key,itm}
linmap_foreach_vclo {v}
  (pf | m, f) = foreach (pf | m, f) where {
  fun foreach {c:clr} {bh:nat} .<bh,c>. (
    pf: !v | t: !rbtree0 (key, itm, c, bh), f: &(!v | key, &itm) -<clo> void
  ) :<> void =
    case+ t of
    | T (_(*c*), !p_k, !p_x, !p_tl, !p_tr) => begin
        foreach (pf | !p_tl, f); f (pf | !p_k, !p_x); foreach (pf | !p_tr, f); fold@ (t)
      end // end of [B]
    | E () => fold@ (t)
  // end of [foreach]
} // end of [linmap_foreach_vclo]

implement{key,itm}
linmap_foreach_cloref (m, f) = let
  val f = __cast (f) where { extern castfn __cast
    (f: (key, &itm) -<cloref> void):<> (!unit_v | key, &itm) -<cloref> void
  } // end of [val]
  typedef clo_type = (!unit_v | key, &itm) -<clo> void
  val (vbox pf_f | p_f) = cloref_get_view_ptr {clo_type} (f)
  prval pf0 = unit_v ()
  val () = $effmask_ref
    (linmap_foreach_vclo<key,itm> {unit_v} (pf0 | m, !p_f))
  prval unit_v () = pf0
in
  // empty
end // end of [linmap_foreach_cloref]

(* ****** ****** *)

implement{key,itm}
linmap_free (m) = _free (m) where {
  fun _free {c:clr} {bh:nat} .<bh,c>.
    (t: rbtree0 (key, itm, c, bh)):<> void = case+ t of
    | ~T (_, _, _, tl, tr) => (_free tl; _free tr) | ~E () => ()
  // end of [_free]
} // end of [linmap_free]

implement{key,itm}
linmap_free_vt (m) = let
  viewtypedef VT = map (key, itm) in
  case+ m of
  | T _ => true where {
      prval () = fold@ (m); prval () = opt_some {VT} (m)
    } // end of [B]
  | E () => false where {
      prval () = opt_none {VT} (m)
    } // end of [E]
end // end of [linmap_free]

(* ****** ****** *)
//
// HX: it can also be implemented based on [foreach]
//
implement{key,itm}
linmap_listize (m) = let
  viewtypedef res_t = List_vt @(key, itm)
  fun aux {c:clr} {bh:nat} .<bh,c>.
    (t: !rbtree0 (key, itm, c, bh), res: res_t):<> res_t =
    case+ t of
    | T (_(*c*), k, x, !p_tl, !p_tr) => let
        val res = aux (!p_tr, res)
        val res = list_vt_cons ((k, x), res)
        val res = aux (!p_tl, res)
        prval () = fold@ (t)
      in
        res
      end // end of [B]
    | E () => (fold@ (t); res)
  // end of [aux]
in
  aux (m, list_vt_nil)
end // end of [linmap_listize]

(* ****** ****** *)

implement{key,itm}
linmap_listize_free (m) = let
  viewtypedef res_t = List_vt @(key, itm)
  fun aux {c:clr} {bh:nat} .<bh,c>.
    (t: rbtree0 (key, itm, c, bh), res: res_t):<> res_t =
    case+ t of
    | ~T (_(*c*), k, x, tl, tr) => let
        val res = aux (tr, res)
        val res = list_vt_cons ((k, x), res)
        val res = aux (tl, res)
      in
        res
      end // end of [B]
    | ~E () => res
  // end of [aux]
in
  aux (m, list_vt_nil)
end // end of [linmap_listize_free]

(* ****** ****** *)

(* end of [linmap_avltree.dats] *)
