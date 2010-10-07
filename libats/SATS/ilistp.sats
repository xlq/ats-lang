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

dataprop
ilisteq (ilist, ilist) =
  | ilisteq_nil (ilist_nil, ilist_nil) of ()
  | {x:int} {xs1,xs2:ilist}
    ilisteq_cons (
      ilist_cons (x, xs1), ilist_cons (x, xs2)
    ) of
      ilisteq (xs1, xs2)
    // end of [ilisteq_cons]
// end of [ilisteq]

(* ****** ****** *)

dataprop
NTH (x0:int, ilist, int) =
  | {xs:ilist} NTHbas (x0, ilist_cons (x0, xs), 0)
  | {x:int} {xs:ilist} {n:nat}
    NTHind (x0, ilist_cons (x, xs), n+1) of NTH (x0, xs, n)
// end of [NTH]

(* ****** ****** *)

dataprop
LENGTH (ilist, int) =
  | LENGTHnil (ilist_nil, 0) of ()
  | {x:int} {xs:ilist} {n:nat}
    LENGTHcons (ilist_cons (x, xs), n+1) of LENGTH (xs, n)
// end of [LENGTH]

prfun length_istot {xs:ilist} (): [n:nat] LENGTH (xs, n)
prfun length_isfun {xs:ilist} {n1,n2:int}
  (pf1: LENGTH (xs, n1), pf2: LENGTH (xs, n2)): [n1==n2] void
// end of [length_isfun]

(* ****** ****** *)

dataprop
APPEND (ilist, ilist, ilist) =
  | {ys:ilist} APPENDnil (ilist_nil, ys, ys) of ()
  | {x:int} {xs:ilist} {ys:ilist} {zs:ilist}
    APPENDcons (ilist_cons (x, xs), ys, ilist_cons (x, zs)) of APPEND (xs, ys, zs)
// end of [APPEND]

prfun append_istot {xs,ys:ilist} (): [zs:ilist] APPEND (xs, ys, zs)
prfun append_isfun {xs,ys:ilist} {zs1,zs2:ilist}
  (pf1: APPEND (xs, ys, zs1), pf2: APPEND (xs, ys, zs2)): ilisteq (zs1, zs2)
// end of [append_isfun]

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
prfun msetcnt_first
  {x:int} {xs:ilist} (): [n:pos] MSETCNT (x, ilist_cons (x, xs), n)
// end of [msetcnt_first]

(* ****** ****** *)

prfun nth_msetcnt_lemma
  {x:int} {xs:ilist} {i:nat} (pf: NTH (x, xs, i)): [n:pos] MSETCNT (x, xs, n)
// end of [nth_msetcnt_lemma]
prfun msetcnt_nth_lemma
  {x:int} {xs:ilist} {n:pos} (pf: MSETCNT (x, xs, n)): [i:nat] NTH (x, xs, i)
// end of [msetcnt_nth_lemma]

(* ****** ****** *)

dataprop
INSERT (
  x0:int, ilist, int, ilist
) = // INSERT (x0, xs, i, ys): insert x0 in xs at i = ys
  | {xs:ilist}
    INSERTbas (
      x0, xs, 0, ilist_cons (x0, xs)
    ) of () // end of [INSERTbas]
  | {x:int} {xs:ilist} {i:nat} {ys:ilist}
    INSERTind (
      x0, ilist_cons (x, xs), i+1, ilist_cons (x, ys)
    ) of INSERT (x0, xs, i, ys) // end of [INSERTind]
// end of [INSERT]

prfun insert_length_lemma
  {x0:int} {xs:ilist} {i:int} {ys:ilist} {n:nat}
  (pf1: INSERT (x0, xs, i, ys), pf2: LENGTH (xs, n)): LENGTH (ys, n+1)
// end of [insert_length_lemma]

prfun nth_insert_lemma
  {x:int} {xs:ilist} {n:nat}
  (pf: NTH (x, xs, n)): [ys:ilist] INSERT (x, ys, n, xs)
// end of [nth_insert_lemma]

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

prfun permute_insert_lemma
  {x:int} {xs:ilist} {ys:ilist}
  (pf: PERMUTE (ilist_cons (x, xs), ys)): [ys1:ilist] [i:nat] INSERT (x, ys1, i, ys)
// end of [permute_insert_lemma]

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

prfun append_munion_lemma
  {xs,ys,zs:ilist} (pf: APPEND (xs,ys,zs)): MUNION (xs, ys, zs)
// end of [append_munion_lemma]

(* ****** ****** *)

propdef
MSUBSET (xs1:ilist, xs2:ilist) =
  {x0:int} {n1,n2:nat}
  (MSETCNT (x0, xs1, n1), MSETCNT (x0, xs1, n2)) -<prf> [n1 <= n2] void
// end of [MSUBSET]

(* ****** ****** *)

(*
dataprop
MSETALL (P: int -> prop, ilist) =
  | MSETALLnil (P, ilist_nil) of ()
  | {x:int} {xs:ilist}
    MSETALLcons (P, ilist_cons (x, xs)) of (P x, MSETALL (P, xs))
// end of [MSETALL]

prfun msetall_trans
  {P1:int->prop} {P2:int->prop} {xs:ilist}
  (pf: MSETALL (P1, xs), fpf: {x:int} P1 x -<prf> P2 x): MSETALL (P2, xs)
// end of [msetall_trans]
*)

(* ****** ****** *)

(*
propdef LT (x0:int) (x:int) = [x0 < x] void
propdef LTB (x0:int, xs:ilist) = MSETALL (LT x0, xs)
propdef LTE (x0:int) (x:int) = [x0 <= x] void
propdef LTEB (x0:int, xs:ilist) = MSETALL (LTE x0, xs)

propdef GT (x0:int) (x:int) = [x0 > x] void
propdef GTB (x0:int, xs:ilist) = MSETALL (GT x0, xs)
propdef GTE (x0:int) (x:int) = [x0 >= x] void
propdef GTEB (x0:int, xs:ilist) = MSETALL (GTE x0, xs)

dataprop
ISORD (ilist) =
  | ISORDnil (ilist_nil) of ()
  | {x:int} {xs:ilist}
    ISORDcons (ilist_cons (x, xs)) of (ISORD xs, LTEB (x, xs))
// end of [ISORD]
*)

(* ****** ****** *)

(* end of [ilistp.sats] *)
