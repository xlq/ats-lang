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
** A set implementation based on AVL trees
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2011
**
*)

(* ****** ****** *)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no static loading at run-time
#define ATS_DYNLOADFLAG 0 // no dynamic loading at run-time

(* ****** ****** *)

staload "libats/SATS/linset_avltree.sats"

(* ****** ****** *)

sortdef t0p = t@ype

(* ****** ****** *)
//
// a specialized version can be implemented on the spot
//
implement{a}
compare_elt_elt (x1, x2, cmp) = cmp (x1, x2)

(* ****** ****** *)
//
// HX-2010-03-24: this seems to work best!
//
#define HTDF 1 // max height difference
#define HTDF1 %(HTDF+1)
#define HTDF_1 %(HTDF-1)

(* ****** ****** *)

dataviewtype
avltree (
  a:t@ype+, int(*height*)
) =
  | {hl,hr:nat | hl <= hr+HTDF; hr <= hl+HTDF}
    B (a, 1+max(hl,hr)) of
      (int (1+max(hl,hr)), a, avltree (a, hl), avltree (a, hr))
  | E (a, 0)
// end of [datatype avltree]
typedef avltree0 = avltree (void, 0)?

viewtypedef
avltree_inc (a:t@ype, h:int) =
  [h1:nat | h <= h1; h1 <= h+1] avltree (a, h1)
// end of [avltree_inc]

viewtypedef
avltree_dec (a:t@ype, h:int) =
  [h1:nat | h1 <= h; h <= h1+1] avltree (a, h1)
// end of [avltree_dec]

(* ****** ****** *)

assume
set_t0ype_type
  (a:t@ype) = [h:nat] avltree (a, h)
// end of [set_t0ype_type]

(* ****** ****** *)

implement{} linset_make_nil () = E ()

(* ****** ****** *)

implement{}
linset_is_empty (t) =
  case+ t of | B _ => (fold@ t; false) | E () => (fold@ t; true)
// end of [linset_is_empty]

implement{}
linset_isnot_empty (t) =
  case+ t of | B _ => (fold@ t; true) | E () => (fold@ t; false)
// end of [linset_isnot_empty]

(* ****** ****** *)

implement{a}
linset_size (t) = size (t) where {
  fun size {h:nat} .<h>.
    (t: !avltree (a, h)):<> size_t = begin case+ t of
    | B (_(*h*), _(*elt*), !ptl, !ptr) => let
       val sz = (size_of_int1)1 + size (!ptl) + size (!ptr) in (fold@ t; sz)
      end // end of [B]
    | E () => (fold@ t; size_of_int1(0))
  end // end of [size]
} // end of [linset_size]

(* ****** ****** *)

fn{a:t@ype}
avltree_height {h:int}
  (t: !avltree (a, h)):<> int h =
  case+ t of B (h, _, _, _) => (fold@ t; h) | _ =>> 0
// end of [avltree_height]

(* ****** ****** *)

implement{a}
linset_is_member
  (xs, x0, cmp) = aux (xs) where {
  fun aux {h:nat} .<h>.
    (t: !avltree (a, h)):<cloref> bool =
    case+ t of
    | B (_, x, !p_tl, !p_tr) => let
        val sgn = compare_elt_elt (x0, x, cmp)
        val res = if sgn < 0 then
          aux (!p_tl) else (if sgn > 0 then aux (!p_tr) else true)
        // end of [val]
      in
        fold@ (t); res
      end // end of [B]
    | E () => (fold@ (t); false)
  // end of [aux]
} // end of [linset_is_member]

implement{a}
linset_isnot_member (xs, x0, cmp) = ~linset_is_member (xs, x0, cmp)

(* ****** ****** *)

(*
** left rotation for restoring height invariant
*)
fn{a:t0p}
avltree_lrotate
  {hl,hr:nat | hl+HTDF1 == hr}
  {l_h,l_k,l_x,l_tl,l_tr:addr} (
    pf_h: int? @ l_h
  , pf_x: a @ l_x
  , pf_tl: avltree (a, hl) @ l_tl
  , pf_tr: avltree (a, hr) @ l_tr
  | p_h: ptr l_h
  , hl : int hl
  , p_tl: ptr l_tl
  , hr : int hr
  , p_tr: ptr l_tr
  , t: B_unfold (l_h, l_x, l_tl, l_tr)
  ) :<> avltree_inc (a, hr) = let
  val tr = !p_tr
  val+ B {..} {hrl,hrr} (!p_hr, _, !p_trl, !p_trr) = tr
  val hrl = avltree_height<a> (!p_trl)
  and hrr = avltree_height<a> (!p_trr)
in
  if hrl <= hrr+HTDF_1 then let
    val hrl1 = hrl + 1
    val () = !p_h := hrl1
    // () = !p_tl := tl
    val () = !p_tr := !p_trl
    prval () = fold@ (t)
    val () = !p_hr := 1+max(hrl1,hrr)
    val () = !p_trl := t
    // val () = !p_trr := trr
    prval () = fold@ (tr)
  in
    tr // B (1+max(hrl1,hrr), kr, xr, B (hrl1, k, x, tl, trl), trr)
  end else let // [hrl=hrr+2]: deep rotation
    val trl = !p_trl
    val+ B {..} {hrll,hrlr} (!p_hrl, _, !p_trll, !p_trlr) = trl
    val hrll = avltree_height (!p_trll)
    val hrlr = avltree_height (!p_trlr)
    val () = !p_h := 1+max(hl,hrll)
    // val () = !p_tl := tl
    val () = !p_tr := !p_trll
    prval () = fold@ t
    val () = !p_hr := 1+max(hrlr, hrr)
    val () = !p_trl := !p_trlr
    // val () = !p_trr := trr
    prval () = fold@ tr
    val () = !p_hrl := hr
    val () = !p_trll := t
    val () = !p_trlr := tr
    prval () = fold@ (trl)
  in
    trl // B (hr, krl, xrl, B (1+max(hl,hrll), k, x, tl, trll), B (1+max(hrlr,hrr), kr, xr, trlr, trr))
  end // end of [if]
end // end of [avltree_lrotate]

(*
** right rotation for restoring height invariant
*)
fn{a:t0p}
avltree_rrotate
  {hl,hr:nat | hl == hr+HTDF1}
  {l_h,l_k,l_x,l_tl,l_tr:addr} (
    pf_h: int? @ l_h
  , pf_x: a @ l_x
  , pf_tl: avltree (a, hl) @ l_tl
  , pf_tr: avltree (a, hr) @ l_tr
  | p_h: ptr l_h
  , hl : int hl
  , p_tl: ptr l_tl
  , hr : int hr
  , p_tr: ptr l_tr
  , t: B_unfold (l_h, l_x, l_tl, l_tr)
  ) :<> avltree_inc (a, hl) = let
  val tl = !p_tl
  val+ B {..} {hll, hlr} (!p_hl, _, !p_tll, !p_tlr) = tl
  val hll = avltree_height<a> (!p_tll)
  and hlr = avltree_height<a> (!p_tlr)
in
  if hll+HTDF_1 >= hlr then let
    val hlr1 = hlr + 1
    val () = !p_h := hlr1
    val () = !p_tl := !p_tlr
    // () = !p_tr := tr
    prval () = fold@ (t)
    val () = !p_hl := 1+max(hll,hlr1)
    // val () = !p_tll := tll
    val () = !p_tlr := t
    prval () = fold@ (tl)
  in
    tl // B (1+max(hll,hlr1), kl, xl, tll, B (hlr1, k, x, tlr, tr))
  end else let
    val tlr = !p_tlr
    val+ B {..} {hlrl,hlrr} (!p_hlr, _, !p_tlrl, !p_tlrr) = tlr
    val hlrl = avltree_height (!p_tlrl)
    val hlrr = avltree_height (!p_tlrr)
    val () = !p_h := 1+max(hlrr,hr)
    val () = !p_tl := !p_tlrr
    // val () = !p_tr := tr
    prval () = fold@ t
    val () = !p_hl := 1+max(hll,hlrl)
    // val () = !p_tll := tll
    val () = !p_tlr := !p_tlrl
    prval () = fold@ tl
    val () = !p_hlr := hl
    val () = !p_tlrl := tl
    val () = !p_tlrr := t
    prval () = fold@ (tlr)
  in
    tlr // B (hl, klr, xlr, B (1+max(hll,hlrl), kl, xl, tll, tlrl), B (1+max(hlrr,hr), k, x, tlrr, tr))
  end // end of [if]
end // end of [avltree_rrotate]

(* ****** ****** *)

implement{a}
linset_insert
  (xs, x0, cmp) = let
//
fun insert {h:nat} .<h>. (
  t: &avltree (a, h) >> avltree_inc (a, h), x0: a
) :<cloref> #[b:bool] bool b = begin
  case+ t of
  | B {..} {hl,hr}
      (!p_h, !p_x, !p_tl, !p_tr) => let
      prval pf_h = view@ !p_h
      prval pf_x = view@ !p_x
      prval pf_tl = view@ !p_tl
      prval pf_tr = view@ !p_tr        
      val sgn = compare_elt_elt (x0, !p_x, cmp)
    in
      if sgn < 0 then let
        val ans = insert (!p_tl, x0)
        val hl = avltree_height<a> (!p_tl)
        and hr = avltree_height<a> (!p_tr)
      in
        if hl - hr <= HTDF then let
          val () = !p_h := 1+max(hl,hr)
          prval () = fold@ (t)
        in
          ans // B (1+max(hl,hr), k, x, tl, tr)
        end else let // hl = hr+HTDF1
          val () = t := avltree_rrotate<a>
            (pf_h, pf_x, pf_tl, pf_tr | p_h, hl, p_tl, hr, p_tr, t)
        in
          ans
        end // end of [if]
      end else if sgn > 0 then let
        val ans = insert (!p_tr, x0)
        val hl = avltree_height<a> (!p_tl)
        and hr = avltree_height<a> (!p_tr)
      in
        if hr - hl <= HTDF then let
          val () = !p_h := 1+max(hl, hr)
          prval () = fold@ (t)
        in
          ans // B (1+max(hl, hr), k, x, tl, tr)
        end else let // hl+HTDF1 = hr
          val () = t := avltree_lrotate<a>
            (pf_h, pf_x, pf_tl, pf_tr | p_h, hl, p_tl, hr, p_tr, t)
        in
          ans
        end // end of [if]
      end else let (* key already exists *)
        prval () = fold@ t in true // B (h, k, x0, tl, tr)
      end // end of [if]
    end // end of [B]
  | ~E () => let
      val () = t := B (1, x0, E (), E ()) in false // a newly created node 
    end // end of [E]
end // end of [insert]
//
in
//
insert (xs, x0)
//
end // end of [linset_insert]

(* ****** ****** *)

(* end of [linset_avltree.dats] *)
