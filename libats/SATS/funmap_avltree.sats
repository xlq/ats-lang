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

#define ATS_STALOADFLAG 0 // no static loading at run-time

(* ****** ****** *)

abstype map_t0ype_t0ype (key: t@ype, itm: t@ype+)
stadef map = map_t0ype_t0ype

(* ****** ****** *)

typedef cmp (key:t@ype) = (key, key) -<cloref> Sgn
fun{key:t@ype} compare_key_key (x1: key, x2: key, cmp: cmp key):<> Sgn

(* ****** ****** *)

fun{} funmap_make_nil {key,itm:t@ype} ():<> map (key, itm)

(* ****** ****** *)

fun{} funmap_is_nil {key,itm:t@ype} (m: map (key, itm)):<> bool
fun{} funmap_isnot_nil {key,itm:t@ype} (m: map (key, itm)):<> bool

(* ****** ****** *)

// this function is O(n)-time and non-tail-recursive
fun{key,itm:t@ype} funmap_size (m: map (key, itm)):<> Nat

// this function is O(1) // for gathering stats
fun{key,itm:t@ype} funmap_height (m: map (key, itm)):<> Nat

(* ****** ****** *)

fun{key,itm:t@ype}
funmap_search (
  m: map (key, itm), k0: key, cmp: cmp key, res: &itm? >> opt (itm, b)
) :<> #[b:bool] bool b
// end of [funmap_search]

(* ****** ****** *)

fun{key,itm:t@ype} funmap_insert (
    m: map (key, itm), k0: key, x0: itm, cmp: cmp key
  ) :<> map (key, itm)
// end of [funmap_insert]

fun{key,itm:t@ype} funmap_insert_clo (
    m: map (key, itm), k0: key, x0: itm, f: &(itm(*new*), itm) -<clo> itm, cmp: cmp key
  ) :<> map (key, itm)
// end of [funmap_insert_clo]

(* ****** ****** *)

fun{key,itm:t@ype} funmap_remove (
  m: map (key, itm), k0: key, cmp: cmp key, res: &itm? >> opt (itm, b), b: &bool? >> bool b
) :<> #[b:bool] map (key, itm)
// end of [funmap_remove]

(* ****** ****** *)

fun{key,itm:t@ype} funmap_foreach_main {v:view} {vt:viewtype}
  (pf: !v | xs: map (key, itm), f: (!v | key, itm, !vt) -<fun> void, env: !vt):<> void
// end of [funmap_foreach_main]

fun{key,itm:t@ype} funmap_foreach_clo {v:view}
  (pf: !v | xs: map (key, itm), f: &(!v | key, itm) -<clo> void):<> void
// end of [funmap_foreach_clo]

fun{key,itm:t@ype} funmap_foreach_cloref
  (xs: map (key, itm), f: (key, itm) -<cloref> void):<!ref> void
// end of [funmap_foreach_cloref]

(* ****** ****** *)

(* end of [funmap_avltree.sats] *)
