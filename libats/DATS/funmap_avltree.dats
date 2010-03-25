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
** Time: March, 2010 // based on a version done in October, 2008
**
*)

(* ****** ****** *)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading at run-time

(* ****** ****** *)

staload "libats/SATS/funmap_avltree.sats"

(* ****** ****** *)

//
// a specialized version can be implemented on the spot
//
implement{key} compare_key_key (x1, x2, cmp) = cmp (x1, x2)

(* ****** ****** *)

//
// HX-2010-03-24: this seems to work best!
//
#define HTDF 1 // max height difference
#define HTDF1 %(HTDF+1)
#define HTDF_1 %(HTDF-1)

(* ****** ****** *)

datatype avltree (key:t@ype, itm:t@ype+, int(*height*)) =
  | {hl,hr:nat | hl <= hr+HTDF; hr <= hl+HTDF}
    B (key, itm, max(hl,hr)+1) of
      (int (max(hl,hr)+1), key, itm, avltree (key, itm, hl), avltree (key, itm, hr))
  | E (key, itm, 0)
// end of [datatype avltree]

typedef avltree_inc (key:t@ype, itm:t@ype, h:int) =
  [h1:nat | h <= h1; h1 <= h+1] avltree (key, itm, h1)
// end of [avltree_inc]

typedef avltree_dec (key:t@ype, itm:t@ype, h:int) =
  [h1:nat | h1 <= h; h <= h1+1] avltree (key, itm, h1)
// end of [avltree_dec]

(* ****** ****** *)

assume map_t0ype_t0ype (key:t@ype, itm:t@ype) = [h:nat] avltree (key, itm, h)

(* ****** ****** *)

implement{} funmap_make_nil () = E ()

(* ****** ****** *)

implement{}
funmap_is_nil (t) = case+ t of | B _ => false | E () => true
// end of [funmap_is_empty]

implement{}
funmap_isnot_nil (t) = case+ t of | B _ => true | E () => false
// end of [funmap_isnot_empty]

(* ****** ****** *)

implement{key,itm}
funmap_size (t) = size (t) where {
  fun size {h:nat} .<h>.
    (t: avltree (key, itm, h)):<> Nat = begin case+ t of
    | B (_(*h*), _(*key*), _(*itm*), tl, tr) => 1 + size (tl) + size (tr)
    | E () => 0
  end // end of [size]
} // end of [funmap_size]

(* ****** ****** *)

macdef avltree_height (t) =
  case+ ,(t) of B (h, _, _, _, _) => h | E _ => 0
// end of [avltree_height]

implement{key,itm}
funmap_height (t) = avltree_height (t)
// end of [funmap_height]

(* ****** ****** *)

implement{key,itm}
funmap_search
  (t, k0, cmp, res) = search (t, res) where {
  fun search {h:nat} .<h>. (
      t: avltree (key, itm, h), res: &itm? >> opt (itm, b)
    ):<cloref> #[b:bool] bool b = begin
    case+ t of
    | B (_(*h*), k, x, tl, tr) => let
        val sgn = compare_key_key (k0, k, cmp)
      in
        case+ 0 of
        | _ when sgn < 0 => search (tl, res)
        | _ when sgn > 0 => search (tr, res)
        | _ => let
            val () = res := x; prval () = opt_some {itm} (res) in true
          end // end of [_]
      end // end of [B]
    | E () => let
        prval () = opt_none {itm} (res) in false
      end // end of [E]
  end // end of [search]
} // end of [funmap_search]

(* ****** ****** *)

(*
** left rotation for restoring height invariant
*)
fn{key,itm:t@ype}
avltree_lrotate {hl,hr:nat | hl+HTDF1 == hr} (
    k: key, x: itm
  , hl : int hl
  , tl: avltree (key, itm, hl)
  , hr : int hr
  , tr: avltree (key, itm, hr)
  ) :<> avltree_inc (key, itm, hr) = let
  val+ B {..} {hrl,hrr} (_(*hr*), kr, xr, trl, trr) = tr
  val hrl = avltree_height trl : int hrl
  and hrr = avltree_height trr : int hrr
in
  if hrl <= hrr+HTDF_1 then let
    val hrl1 = hrl + 1
  in
    B (1+max(hrl1,hrr), kr, xr, B (hrl1, k, x, tl, trl), trr)
  end else let // [hrl=hrr+2]: deep rotation
    val+ B {..} {hrll,hrlr} (_(*hrl*), krl, xrl, trll, trlr) = trl
    val hrll = avltree_height trll : int hrll
    val hrlr = avltree_height trlr : int hrlr
  in
    B (hr, krl, xrl, B (1+max(hl,hrll), k, x, tl, trll), B (1+max(hrlr,hrr), kr, xr, trlr, trr))
  end // end of [if]
end // end of [avltree_lrotate]

(*
** right rotation for restoring height invariant
*)
fn{key,itm:t@ype}
avltree_rrotate {hl,hr:nat | hl == hr+HTDF1} (
    k: key, x: itm
  , hl: int hl
  , tl: avltree (key, itm, hl)
  , hr: int hr
  , tr: avltree (key, itm, hr)
  ) :<> avltree_inc (key, itm, hl) = let
  val+ B {..} {hll, hlr} (_(*hl*), kl, xl, tll, tlr) = tl
  val hll = avltree_height tll : int hll
  and hlr = avltree_height tlr : int hlr
in
  if hll+HTDF_1 >= hlr then let
    val hlr1 = hlr + 1
  in
    B (1+max(hll,hlr1), kl, xl, tll, B (hlr1, k, x, tlr, tr))
  end else let
    val+ B {..} {hlrl,hlrr} (_(*hlr*), klr, xlr, tlrl, tlrr) = tlr
    val hlrl = avltree_height tlrl : int hlrl
    val hlrr = avltree_height tlrr : int hlrr
  in
    B (hl, klr, xlr, B (1+max(hll,hlrl), kl, xl, tll, tlrl), B (1+max(hlrr,hr), k, x, tlrr, tr))
  end // end of [if]
end // end of [avltree_rrotate]

(* ****** ****** *)

implement{key,itm} funmap_insert
  (m, k0, x0, cmp) = insert (m) where {
  fun insert {h:nat} .<h>. (t: avltree (key, itm, h))
    :<cloref> avltree_inc (key, itm, h) = begin case+ t of
    | B {..} {hl,hr} (h, k, x, tl, tr) => let
        val sgn = compare_key_key (k0, k, cmp)
      in
        if sgn < 0 then let
          val [hl:int] tl = insert (tl)
          val hl = avltree_height (tl) : int hl
          and hr = avltree_height (tr) : int hr
        in
          if hl - hr <= HTDF then begin
            B (1+max(hl,hr), k, x, tl, tr)
          end else begin // hl = hr+HTDF1
            avltree_rrotate (k, x, hl, tl, hr, tr)
          end // end of [if]
        end else if sgn > 0 then let
          val [hr:int] tr = insert (tr)
          val hl = avltree_height (tl) : int hl
          and hr = avltree_height (tr) : int hr
        in
          if hr - hl <= HTDF then begin
            B (1+max(hl, hr), k, x, tl, tr)
          end else begin // hl+HTDF1 = hr
            avltree_lrotate (k, x, hl, tl, hr, tr)
          end // end of [if]
        end else begin (* sgn = 0: item already exists *)
          B (h, k, x0, tl, tr)
        end // end of [if]
      end // end of [B]
    | E () => begin
        B (1, k0, x0, E (), E ())
      end // end of [E]
  end // end of [insert]
} // end of [funmap_insert]

(* ****** ****** *)

implement{key,itm} funmap_insert_clo
  (m, k0, x0, f, cmp) = insert (m, f) where {
  fun insert {h:nat} .<h>.
    (t: avltree (key, itm, h), f: &(itm, itm) -<clo> itm)
    :<cloref> avltree_inc (key, itm, h) = begin case+ t of
    | B {..} {hl,hr} (h, k, x, tl, tr) => let
        val sgn = compare_key_key (k0, k, cmp)
      in
        if sgn < 0 then let
          val [hl:int] tl = insert (tl, f)
          val hl = avltree_height (tl) : int hl
          and hr = avltree_height (tr) : int hr
        in
          if hl - hr <= HTDF then begin
            B (1+max(hl,hr), k, x, tl, tr)
          end else begin // hl = hr+HTDF1
            avltree_rrotate (k, x, hl, tl, hr, tr)
          end // end of [if]
        end else if sgn > 0 then let
          val [hr:int] tr = insert (tr, f)
          val hl = avltree_height (tl) : int hl
          and hr = avltree_height (tr) : int hr
        in
          if hr - hl <= HTDF then begin
            B (1+max(hl, hr), k, x, tl, tr)
          end else begin // hl+HTDF1 = hr
            avltree_lrotate (k, x, hl, tl, hr, tr)
          end // end of [if]
        end else begin (* sgn = 0: item already exists *)
          B (h, k, f (x0, x), tl, tr)
        end // end of [if]
      end // end of [B]
    | E () => begin
        B (1, k0, x0, E (), E ())
      end // end of [E]
  end // end of [insert]
} // end of [funmap_insert_clo]

(* ****** ****** *)

fun{key,itm:t@ype} avltree_takeout_min {h:pos} .<h>. (
    t: avltree (key, itm, h)
  , k0: &key? >> key
  , x0: &itm? >> itm
  ) :<> avltree_dec (key, itm, h) = let
  val+ B {..} {hl,hr} (_, k, x, tl, tr) = t
in
  case+ tl of
  | B _ => let
      val [hl:int] tl = avltree_takeout_min<key,itm> (tl, k0, x0)
      val hl = avltree_height (tl) : int hl
      and hr = avltree_height (tr) : int hr
    in
      if hr - hl <= HTDF then begin
        B (max(hl,hr)+1, k, x, tl, tr)
      end else begin // hl+HTDF1 = hr
       avltree_lrotate (k, x, hl, tl, hr, tr)
      end // end of [if]
    end // end of [B]
  | E () => (k0 := k; x0 := x; tr)
end // end of [avltree_takeout_min]

implement{key,itm}
funmap_remove (m, k0, cmp, res, b) = remove (m, res, b) where {
  fun remove {h:nat} .<h>. (
      t: avltree (key, itm, h), res: &itm? >> opt (itm, b), b: &bool? >> bool b
    ) :<cloref> #[b:bool] avltree_dec (key, itm, h) = begin
    case+ t of
    | B {..} {hl,hr} (h, k, x, tl, tr) => let
        val sgn = compare_key_key (k0, k, cmp)
      in
        case+ 0 of
        | _ when sgn < 0 => let
            val [hl:int] tl = remove (tl, res, b)
            val hl = avltree_height (tl) : int hl
            and hr = avltree_height (tr) : int hr
          in
            if hr - hl <= HTDF then begin
              B (1+max(hl,hr), k, x, tl, tr)
            end else begin // hl+HTDF1 = hr
              avltree_lrotate (k, x, hl, tl, hr, tr)
            end // end of [if]
          end // end of [sgn < 0]
        | _ when sgn > 0 => let
            val [hr:int] tr = remove (tr, res, b)
            val hl = avltree_height (tl) : int hl
            and hr = avltree_height (tr) : int hr
          in
            if hl - hr <= HTDF then begin
              B (1+max(hl,hr), k, x, tl, tr)
            end else begin // hl=hr+HTDF1
              avltree_rrotate (k, x, hl, tl, hr, tr)
            end // end of [if]
          end // end of [sgn > 0]
        | _ (*sgn = 0*) => let
            val () = res := x
            prval () = opt_some (res)
            val () = b := true
          in
            case+ tr of
            | B _ => let
                var k_min: key? and x_min: itm?
                val [hr:int] tr = avltree_takeout_min<key,itm> (tr, k_min, x_min)
                val hl = avltree_height (tl) : int hl
                and hr = avltree_height (tr) : int hr
              in
                if hl - hr <= HTDF then begin
                  B (1+max(hl,hr), k, x, tl, tr)
                end else begin // hl=hr+HTDF1
                  avltree_rrotate (k, x, hl, tl, hr, tr)
                end // end of [if]
              end // end of [B]
            | E _ => tl
          end // end of [sgn = 0]
      end // end of [B]
    | E () => let
        prval () = opt_none {itm} (res); val () = b := false in t
      end // end of [E]
  end // end of [remove]
} // end of [funmap_remove]

(* ****** ****** *)

(*
fun{key,itm:t@ype} funmap_foreach_main {v:view} {vt:viewtype}
  (pf: !v | m: map (key, itm), f: (!v | key, itm, !vt) -<clo> void, env: !vt):<> void
// end of [funmap_foreach_main]
*)

implement{key,itm}
funmap_foreach_main {v} {vt}
  (pf | m, f, env) = foreach (pf | m, env) where {
  fun foreach {h:nat} .<h>.
    (pf: !v | t: avltree (key, itm, h), env: !vt):<cloref> void =
    case+ t of
    | B (_(*h*), k, x, tl, tr) => begin
        foreach (pf | tl, env); f (pf | k, x, env); foreach (pf | tr, env)
      end // end of [B]
    | E () => ()
  // end of [foreach]
} // end of [funmap_foreach_main]

implement{key,itm}
funmap_foreach_clo {v}
  (pf | m, f) = foreach (pf | m, f) where {
  fun foreach {h:nat} .<h>.
    (pf: !v | t: avltree (key, itm, h), f: &(!v | key, itm) -<clo> void):<> void =
    case+ t of
    | B (_(*h*), k, x, tl, tr) => begin
        foreach (pf | tl, f); f (pf | k, x); foreach (pf | tr, f)
      end // end of [B]
    | E () => ()
  // end of [foreach]
} // end of [funmap_foreach_clo]

implement{key,itm}
  funmap_foreach_cloref (m, f) = let
  val f = __cast (f) where { extern castfn __cast
    (f: (key, itm) -<cloref> void):<> (!unit_v | key, itm) -<cloref> void
  } // end of [val]
  typedef clo_type = (!unit_v | key, itm) -<clo> void
  val (vbox pf_f | p_f) = cloref_get_view_ptr {clo_type} (f)
  prval pf0 = unit_v ()
  val () = $effmask_ref
    (funmap_foreach_clo<key,itm> {unit_v} (pf0 | m, !p_f))
  prval unit_v () = pf0
in
  // empty
end // end of [funmap_foreach_cloref]

(* ****** ****** *)

(* end of [funmap_avltree.dats] *)