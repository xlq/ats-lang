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
// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: October, 2011
//
(* ****** ****** *)

%{#
#include "contrib/graphviz/CATS/gvc.cats"
%} // end of [%{#]

(* ****** ****** *)

(*
// HX:
// declared in gvcext.h
typedef struct GVJ_s GVJ_t;
typedef struct GVC_s GVC_t;
*)
//
absviewtype GVJptr (l:addr)
viewtypedef GVJptr0 = [l:addr] GVJptr (l)
viewtypedef GVJptr1 = [l:addr | l >  null] GVJptr (l)
//
absviewtype GVCptr (l:addr)
viewtypedef GVCptr0 = [l:addr] GVCptr (l)
viewtypedef GVCptr1 = [l:addr | l >  null] GVCptr (l)
//
absviewtype pgraph_viewtype (l:addr) = ptr
stadef pgraph = pgraph_viewtype
//
(* ****** ****** *)

(*
GVC_t *gvContext(void)
*)
fun gvContext (): GVCptr0 = "mac#atsctrb_gvContext"
fun gvContext_exn (): GVCptr1 = "mac#atsctrb_gvContext_exn"
//
// HX: returning the number of accumulated errors
//
fun gvFreeContext0
  (gvc: GVCptr0): int = "mac#atsctrb_gvFreecContext0"
fun gvFreeContext1
  (gvc: GVCptr1): int = "mac#atsctrb_gvFreecContext1"
//
(* ****** ****** *)

absview gvLayout_v (addr(*gvc*), addr(*graph*))

(*
int gvLayout(GVC_t *gvc, graph_t *g, const char *engine)
*)
fun gvLayout {l1,l2:agz} (
  gvc: !GVCptr l1, g: pgraph l2
) : [i:int | i <= 0] (option_v (gvLayout_v (l1, l2), i >= 0) | int i)

(* ****** ****** *)

(* end of [gvc.sats] *)
