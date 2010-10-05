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
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October, 2010
//
(* ****** ****** *)
//
// HX: reasoning about integer sequences and multisets
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0 // there is no need for staloading at run-time

(* ****** ****** *)

datasort ilist =
  | ilist_nil of () | ilist_cons of (int, ilist)
// end of [ilist]

(* ****** ****** *)

dataprop
LENGTH (ilist, int) =
  | LENGTHnil (ilist_nil, 0) of ()
  | {x:int} {xs:ilist} {n:nat}
    LENGTHcons (ilist_cons (x, xs), n+1) of LENGTH (xs, n)
// end of [LENGTH]

(* ****** ****** *)

prfun length_istot {xs:ilist} (): [n:nat] LENGTH (xs, n)
prfun length_isfun {xs:ilist} {n1,n2:int}
  (pf1: LENGTH (xs, n1), pf2: LENGTH (xs, n2)): [n1==n2] void
// end of [length_isfun]

(* ****** ****** *)

stadef b2i = int_of_bool

(* ****** ****** *)

dataprop
MSETCNT (x0:int, ilist, int) =
  | MSETCNTnil (x0, ilist_nil, 0) of ()
  | {x:int} {xs:ilist} {n:nat}
    MSETCNTcons (x0, ilist_cons (x, xs), n+b2i(x0==x)) of MSETCNT (x0, xs, n)
// end of [MSETCNT]

prfun msetcnt_istot
  {x0:int} {xs:ilist} (): [n:nat] MSETCNT (x0, xs, n)
prfun msetcnt_isfun
  {x0:int} {xs:ilist} {n1,n2:int} (
    pf1: MSETCNT (x0, xs, n1), pf2: MSETCNT (x0, xs, n2)
  ) : [n1==n2] void
// end of [msetcnt_isfun]

(* ****** ****** *)

propdef
PERMUTE (xs1:ilist, xs2:ilist) =
  {x0:int} {n:nat} MSETCNT (x0, xs1, n) -<prf> MSETCNT (x0, xs2, n)
// end of [PERMUTE]

prfun permute_refl {xs:ilist} (): PERMUTE (xs, xs)
prfun permute_symm
  {xs1,xs2:ilist} (pf: PERMUTE (xs1, xs2)): PERMUTE (xs2, xs1)
prfun permute_trans {xs1,xs2,xs3:ilist}
  (pf1: PERMUTE (xs1, xs2), pf2: PERMUTE (xs2, xs3)): PERMUTE (xs1, xs3)

prfun permute_length_lemma
  {xs1,xs2:ilist} {n:nat}
  (pf1: PERMUTE (xs1, xs2), pf2: LENGTH (xs1, n)): LENGTH (xs2, n)
// end of [permute_length_lemma]

(* ****** ****** *)

propdef
MUNION (xs1:ilist, xs2:ilist, xs3:ilist) =
  {x0:int} {n1,n2:nat}
  (MSETCNT (x0, xs1, n1), MSETCNT (x0, xs2, n2)) -<prf> MSETCNT (x0, xs3, n1+n2)
// end of [MUNION]

(* ****** ****** *)

propdef
MSUBSET (xs1:ilist, xs2:ilist) =
  {x0:int} {n1,n2:nat}
  (MSETCNT (x0, xs1, n1), MSETCNT (x0, xs1, n2)) -<prf> [n1 <= n2] void
// end of [MSUBSET]

(* ****** ****** *)

(* end of [ilistp.sats] *)
