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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(*
**
** A hashtable implementation
** where buckets are represented as linked lists
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: March, 2010 // based on a version on in October, 2008
**
*)

(* ****** ****** *)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no static loading at run-time

(* ****** ****** *)

typedef hash (key: t@ype) = (key) -<cloref> ulint
typedef eq (key: t@ype) = (key, key) -<cloref> bool

absviewtype HASHTBLptr (key:t@ype, itm:viewt@ype+, l:addr)
viewtypedef HASHTBLptr0
  (key:t@ype, itm:viewt@ype) = [l:addr] HASHTBLptr (key, itm, l)
// end of [HASHTBLptr0]
viewtypedef HASHTBLptr1
  (key:t@ype, itm:viewt@ype) = [l:addr | l <> null] HASHTBLptr (key, itm, l)
// end of [HASHTBLptr1]

castfn ptr_of_HASHTBLptr
  {key:t@ype} {itm:viewt@ype} {l:addr} (x: !HASHTBLptr (key, itm, l)):<> ptr l
overload ptr_of with ptr_of_HASHTBLptr

(* ****** ****** *)

fun{key:t@ype}
hash_key (x: key, fhash: hash key):<> ulint
// end of [hash_key]

fun{key:t@ype}
equal_key_key (x1: key, x2: key, feq: eq key):<> bool
// end of [equal_key_key]

(* ****** ****** *)

fun hashtbl_size // the (array) size of the hashtable
  {key:t@ype;itm:viewt@ype} {l:anz} (p: !HASHTBLptr (key, itm, l)):<> size_t
// end of [hashtbl_size]

fun hashtbl_total // the total number of elements present in the hashtable
  {key:t@ype;itm:viewt@ype} {l:anz} (tbl: !HASHTBLptr (key, itm, l)):<> size_t
// end of [hashtbl_total]

fun{key:t@ype;itm:t@ype} // clear the hashtable: all the chains are freed
hashtbl_clear {l:anz} (ptbl: !HASHTBLptr (key, itm, l)):<> void
// end of [hashtbl_clear]

fun{key:t@ype;itm:t@ype} // clear the hashtable: all the chains are freed
hashtbl_clear_vt
  {l:anz} (ptbl: !HASHTBLptr (key, itm, l), f: (&itm >> itm?) -<> void):<> void
// end of [hashtbl_clear_vt]

(* ****** ****** *)

//
// HX-2010-03-20:
// if the returned pointer is used, it must be done before the hashtable
// is changed!
//
fun{key:t@ype;itm:viewt@ype} // unsafe but ...
hashtbl_search_ref {l:anz} (ptbl: !HASHTBLptr (key, itm, l), k0: key): Ptr
// end of [hashtbl_search_ptr]

//
// HX-2010-03-20:
// this one is a safe version, but it can only handle non-linear items
//
fun{key:t@ype;itm:t@ype}
hashtbl_search {l:anz} (ptbl: !HASHTBLptr (key, itm, l), k0: key): Option_vt itm
// end of [hashtbl_search]

(* ****** ****** *)

fun{key:t@ype;itm:viewt@ype}
hashtbl_insert {l:anz} (ptbl: !HASHTBLptr (key, itm, l), k: key, i: itm):<> void
// end of [hashtbl_insert]

fun{key:t@ype;itm:viewt@ype}
hashtbl_remove {l:anz} (ptbl: !HASHTBLptr (key, itm, l), k0: key): Option_vt itm
// end of [hashtbl_remove]

(* ****** ****** *)

fun{key:t@ype;itm:viewt@ype}
hashtbl_foreach_clo {v:view} {l:anz}
  (pf: !v | ptbl: !HASHTBLptr (key, itm, l), f: &(!v | key, &itm) -<clo> void):<!ref> void
// end of [hashtbl_foreach_clo]

fun{key:t@ype;itm:viewt@ype}
hashtbl_foreach_cloref {l:anz}
  (ptbl: !HASHTBLptr (key, itm, l), f: !(key, &itm) -<cloref> void):<!ref> void
// end of [hashtbl_foreach_cloref]

(* ****** ****** *)

fun hashtbl_make {key:t@ype;itm:viewt@ype}
  (fhash: hash key, feq: eq key): HASHTBLptr1 (key, itm)
// end of [hashtbl_make]

fun hashtbl_make_hint {key:t@ype;itm:viewt@ype}
  (fhash: hash key, feq: eq key, hint: size_t): HASHTBLptr1 (key, itm)
  = "atslib_hashtbl_make_hint"
// end of [hashtbl_make_hint]

(* ****** ****** *)

fun hashtbl_free
  {key:t@ype;itm:t@ype} {l:anz} (tbl: HASHTBLptr (key, itm, l)): void
  = "atslib_hashtbl_free"
// end of [hashtbl_free]

fun hashtbl_free_null
  {key:t@ype;itm:viewt@ype} (tbl: HASHTBLptr (key, itm, null)): void
  = "atslib_hashtbl_free_null"
// end of [hashtbl_free_exn]

//
// HX-2010-03-21:
// [hashtbl_clear_vt] may need to be called first to clear up the hashtable
//
fun hashtbl_free_vt
  {key:t@ype;itm:viewt@ype} {l:anz}
  (tbl: !HASHTBLptr (key, itm, l) >> opt (HASHTBLptr (key, itm, l), i > 0))
  : #[i:two] int i = "atslib_hashtbl_free_vt"
// end of [hashtbl_free_vt]

(* ****** ****** *)

(* end of [hashtable_chain.sats] *)
