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

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2010
//

(* ****** ****** *)

//
// HX-2010-02-28:
// In any acconts, [glist] is a terrible package for ATS to incorporate.
// It is simply a _big_ mess, and I have tried my best to make some sense
// out of this mess!
//

(* ****** ****** *)

%{#
#include "contrib/glib/CATS/glib/glist.cats"
%} // end of [%{#]

(* ****** ****** *)

//
// HX-2010-02-27: only need for individual testing
// staload "contrib/glib/SATS/gtypes.sats"
//

(* ****** ****** *)

sortdef vwtp = viewtype

absviewtype GList_ptr (a:viewtype+, n:int) // = GList*
viewtypedef GList_ptr0 (a:vwtp) = [n:nat] GList_ptr (a, n)
viewtypedef GList_ptr1 (a:vwtp) = [n:pos] GList_ptr (a, n)

(* ****** ****** *)

fun g_list_new_nil {a:vwtp}
  (): GList_ptr (a, 0) = "#atsctrb_g_list_new_nil"
// end of [g_list_new_nil]

fun glist_free_nil {a:vwtp} (xs: GList_ptr (a, 0)):<> void
  = "#atsctrb_g_list_free_nil"
// end of [glist_free_nil]
  
(* ****** ****** *)

fun g_list_free
  {a:vwtp} (list: GList_ptr0 (a?)): void = "#atsctrb_g_list_free"
// end of [g_list]

(* ****** ****** *)

fun g_list_append
  {a:vwtp} {n:nat} // its complexity is O(n)
  (list: GList_ptr (a, n), x: !a >> a?!): GList_ptr (a, n+1)
  = "#atsctrb_g_list_append"
// end of [g_list_append]

(* ****** ****** *)

fun g_list_prepend
  {a:vwtp} {n:nat} // its complexity is O(1)
  (list: GList_ptr (a, n), x: !a >> a?!): GList_ptr (a, n+1)
  = "#atsctrb_g_list_prepend"
// end of [g_list_prepend]

(* ****** ****** *)

fun g_list_length {a:vwtp} {n:nat}
  (list: !GList_ptr (a, n)): gint n = "#atsctrb_g_list_length"
// end of [g_list_length]

(* ****** ****** *)

fun g_list_insert // its complexity is O(i)
  {a:vwtp} {n,i:nat | i <= n}
  (list: GList_ptr (a, n), x: !a >> a?!, i: gint i): GList_ptr (a, n+1)
  = "#atsctrb_g_list_insert"
// end of [g_list_insert]

fun g_list_insert_sorted
  {a:vwtp} {n:nat} ( // its complexity is O(n)
    list: GList_ptr (a, n), x: !a >> a?!, cmp: (!a, !a) -<fun> gint
  ) : GList_ptr (a, n+1)
  = "#atsctrb_g_list_insert_sorted"
// end of [g_list_insert_sorted]

(* ****** ****** *)

fun g_list_concat {a:vwtp} {n1,n2:nat}
  (list1: GList_ptr (a,n1), list2: GList_ptr (a,n2))
  : GList_ptr (a,n1+n2) = "#atsctrb_g_list_concat"
// end of [g_list_concat]

(* ****** ****** *)

fun g_list_copy {a:type} {n:nat}
  (list: !GList_ptr (a,n)): GList_ptr (a,n) = "#atsctrb_g_list_copy"
// end of [g_list_copy]

(* ****** ****** *)

fun g_list_reverse {a:vwtp} {n:nat}
  (list: GList_ptr (a,n)): GList_ptr (a,n) = "#atsctrb_g_list_reverse"
// end of [g_list_reverse]

(* ****** ****** *)

//
// HX-2010-02-28:
// these sorting functions are based on mergesort implementation
//
fun g_list_sort {a:vwtp} {n:nat}
  (list: GList_ptr (a, n), cmp: (!a, !a) -<fun> gint): GList_ptr (a, n)
  = "#atsctrb_g_list_sort"
// end of [g_list_sort]

fun g_list_sort_with_data {a:vwtp} {vt:viewtype} {n:nat}
  (list: GList_ptr (a, n), cmp: (!a, !a, !vt) -<fun> gint, env: !vt)
  : GList_ptr (a, n) = "#atsctrb_g_list_sort_with_data"
// end of [g_list_sort_with_data]

(* ****** ****** *)

fun g_list_foreach {a:vwtp} {vt:viewtype} {n:nat}
  (list: !GList_ptr (a, n), f: (!a, !vt) -<fun> void, env: !vt)
  : void = "#atsctrb_g_list_foreach"
// end of [g_list_foreach]

(* ****** ****** *)

fun g_list_nth_data {a:type}
  {n,i:nat | i < n} (list: !GList_ptr (a, n), i: int i): a
  = "#atsctrb_g_list_nth_data"
// end of [g_list_nth_data]

(* ****** ****** *)

fun g_list_index {a:type} {n:nat}
  (list: !GList_ptr (a, n), x: !a): [i:int | ~1 <= i; i < n] gint i
  = "#atsctrb_g_list_index"
// end of [g_list_index]
  
(* ****** ****** *)

(* end of [glist.sats] *)
