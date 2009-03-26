(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS/Anairiats - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
 * Free Software Foundation; either version 3, or (at  your  option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

// list implementation

#define nil list_nil
#define :: list_cons

fun list_is_cons {a:type} {n:nat} (xs: list (a, n)): bool (n > 0)

fun list_append {a:type} {i,j:nat}
  (xs: list (a, i), ys: list (a, j)):<> list (a, i+j)
overload + with list_append

fun list_extend {a:type} {n:nat}
  (xs: list (a, n), x: a):<> list (a, n+1)

(* ****** ****** *)

fun list_foreach_main {a:type} {v:view} {vt:viewtype} {f:eff}
  (pf: !v | xs: List a, f: (!v | a, !vt) -<f> void, env: !vt):<f> void

fun list_foreach_fun {a:type} {f:eff}
  (xs: List a, f: a -<f> void):<f> void

fun list_foreach_cloptr {a:type} {f:eff}
  (xs: List a, f: !a -<cloptr,f> void):<f> void

(* ****** ****** *)

fun list_length {a:type} {n:nat} (xs: list (a, n)):<> int n

(* ****** ****** *)

fun list_map_main {a,b:type} {v:view} {vt:viewtype} {n:nat} {f:eff}
  (pf: !v | xs: list (a, n), f: (!v | a, !vt) -<f> b, env: !vt):<f> list (b, n)

fun list_map_fun {a,b:type} {n:nat} {f:eff}
  (xs: list (a, n), f: a -<f> b):<f> list (b, n)

fun list_map_cloptr {a,b:type} {n:nat} {f:eff}
  (xs: list (a, n), f: !a -<cloptr,f> b):<f> list (b, n)

(* ****** ****** *)

fun list_revapp {a:type} {i,j:nat}
  (xs: list (a, i), ys: list (a, j)):<> list (a, i+j)

fun list_reverse {a:type} {n:nat} (xs: list (a, n)):<> list (a, n)

(* ****** ****** *)

fun list_length_compare
  {a1,a2:type} {n1,n2:nat} (xs1: list (a1, n1), xs2: list (a2, n2))
  :<> [i:int | sgn_r (n1-n2, i)] int i

(* ****** ****** *)

fun{a:t@ype} list_vt_copy
  {n:nat} (xs: !list_vt (a, n)):<> list_vt (a, n)

fun list_vt_copy__boxed {a:type}
  {n:nat} (xs: !list_vt (a, n)):<> list_vt (a, n)
  
(* ****** ****** *)

fun {a:t@ype} list_vt_free {n:nat} (xs: list_vt (a, n)):<> void
fun list_vt_free__boxed {a:type} {n:nat} (xs: list_vt (a, n)):<> void

(* ****** ****** *)

fun{a:viewt@ype} list_vt_length {n:nat} (xs: !list_vt (a, n)):<> int n
fun list_vt_length__boxed {a:viewtype} {n:nat} (xs: !list_vt (a, n)):<> int n

(* ****** ****** *)

fun list_vt_append {a:viewtype} {n1,n2:nat}
  (xs1: list_vt (a, n1), xs2: list_vt (a, n2)): list_vt (a, n1+n2)

fun list_vt_prefix {a:viewtype} {n,i:nat | i <= n}
  (xs: &list_vt (a, n) >> list_vt (a, n-i), i: int i): list_vt (a, i)

fun list_vt_revapp {a:viewtype} {m,n:nat}
  (xs: list_vt (a, m), ys: list_vt (a, n)):<> list_vt (a, m+n)

fun list_vt_reverse {a:viewtype} {n:nat} (xs: list_vt (a, n))
  :<> list_vt (a, n)

(* ****** ****** *)

fun list_vt_revapp_list {a:type} {m,n:nat}
  (xs: list_vt (a, m), ys: list (a, n)):<> list (a, m+n)

fun list_vt_reverse_list {a:type} {n:nat} (xs: list_vt (a, n))
  :<> list (a, n)

(* ****** ****** *)

(* end of [ats_list.sats] *)
