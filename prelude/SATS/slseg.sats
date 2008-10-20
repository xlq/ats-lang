(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
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

#include "prelude/params.hats"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [slseg.sats] starts!\n"

#endif

(* ****** ****** *)

%{#

#include "prelude/CATS/slseg.cats"

%}

(* ****** ****** *)

dataview slseg_v (a:viewt@ype+, addr, addr, int) =
  | {n:nat} {l1,l2,l3:addr}
    slseg_v_cons (a, l1, l3, n+1) of (
      free_gc_v l1, (a, ptr l2) @ l1, slseg_v (a, l2, l3, n)
    ) // end of [slseg_v_cons]
  | {l:addr} slseg_v_nil (a, l, l, 0)

viewdef sllst_v (a: viewt@ype, l:addr, n:int) = slseg_v (a, l, null, n)
  
(* ****** ****** *)

prfun slseg_v_extend {a:viewt@ype} {l1,l2,l3:addr} {n:nat}
  (pf_seg: slseg_v (a, l1, l2, n), pf_gc: free_gc_v l2, pf_at: (a, ptr l3) @ l2)
  :<prf> slseg_v (a, l1, l3, n+1)

(* ****** ****** *)

prfun slseg_v_append {a:viewt@ype} {l1,l2,l3:addr} {n1,n2:nat}
  (pf1_seg: slseg_v (a, l1, l2, n1), pf2_seg: slseg_v (a, l2, l3, n2))
  :<prf> slseg_v (a, l1, l3, n1+n2)

(* ****** ****** *)

fun{a:viewt@ype} slseg_foreach_cloptr
   {v:view} {l1,l2:addr} {n:nat} {f:eff} (
    pf: !v, pf_seg: !slseg_v (a, l1, l2, n)
  | p: ptr l1, n: int n, f: !(!v | &a) -<cloptr,f> void
  ) :<f> void

(* ****** ****** *)

fun list_vt_of_sllst {a:viewt@ype} {n:nat} {l:addr}
  (pf_seg: sllst_v (a, l, n) | p: ptr l): list_vt (a, n)
  = "atspre_list_vt_of_sllst"

fun sllst_of_list_vt {a:viewt@ype} {n:nat} {l:addr}
  (xs: list_vt (a, n)): [l:addr] (sllst_v (a, l, n) | ptr l)
  = "atspre_sllst_list_vt_of"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [slseg_v.sats] finishes!\n"

#endif

(* end of [slseg_v.sats] *)
