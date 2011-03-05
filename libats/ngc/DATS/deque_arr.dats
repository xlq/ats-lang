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
** An array-based deque implementation
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

#define ATS_DYNLOADFLAG 0 // no static loading at run-time

(* ****** ****** *)

staload "libats/ngc/SATS/deque_arr.sats"

(* ****** ****** *)

absview DEQUEarr_v (
  a:viewt@ype+
, m:int, n:int
, lft:addr, rgt:addr
, l_beg:addr, l_end:addr
) // end of [DEQUEarr_v]

extern
prfun DEQUEarr_v_encode
  {a:viewt@ype}
  {m:nat} {lft:addr} {ofs:int} (
  pfmul: MUL (m, sizeof a, ofs)
, pfarr: array_v (a?, m, lft)
) :<prf> DEQUEarr_v (a, m, 0, lft, lft+ofs, lft, lft)
// end of [DEQUEarr_v_encode]

extern
prfun DEQUEarr_v_decode
  {a:viewt@ype}
  {m:nat}
  {lft,rgt,l_beg,l_end:addr} (
  pf: DEQUEarr_v (a, m, 0, lft, rgt, l_beg, l_end)
) :<prf> array_v (a?, m, lft) // end of [DEQUEarr_v_decode]

extern
prfun DEQUEarr_v_clear
  {a:t@ype}
  {m,n:nat}
  {lft,rgt,l_beg,l_end:addr} (
  pf: DEQUEarr_v (a, m, n, lft, rgt, l_beg, l_end)
) :<prf> DEQUEarr_v (a, m, 0, lft, rgt, lft, lft)
// end of [DEQUEarr_v_clear]

(* ****** ****** *)

viewtypedef DEQUE_vt (
  a:viewt@ype
, m:int, n:int
, lft:addr, rgt:addr
, l_beg:addr, l_end:addr
) = $extype_struct "atslib_ngc_deque_arr_DEQUE" of {
  cap= size_t m
, nitm= size_t n
, qarr_lft= ptr lft
, qarr_rgt= ptr rgt
, qarr_beg= ptr l_beg
, qarr_end= ptr l_end
, pfqarr= DEQUEarr_v (a, m, n, lft, rgt, l_beg, l_end)
, pfqarr_gc= free_gc_v (a, m, lft)
} // end of [DEQUE_vt]

typedef DEQUE0_vt
  (a:viewt@ype) = DEQUE_vt (a, 0, 0, null, null, null, null)?
// end of [DEQUE0_vt]

(* ****** ****** *)

absprop
DEQUEptrprv_p (
  a:viewt@ype, lft:addr, rgt:addr, l:addr, l_prv:addr
) // end of [DEQUEptrprv_p]

extern
fun{a:viewt@ype}
DEQUEptrprv
  {m,n:nat}
  {lft,rgt,l_beg,l_end:addr}
  {l:addr} (
  q: &DEQUE_vt (a, m, n, lft, rgt, l_beg, l_end)
, p: ptr l
) :<> [l_prv:addr] (DEQUEptrprv_p (a, lft, rgt, l, l_prv) | ptr l_prv)
// end of [DEQUEptrprv_p]

implement{a}
DEQUEptrprv {m,n}
  {lft,rgt,l_beg,l_end} {l} (q, p) = let
  var p: Ptr = p
  val () = if p <= q.qarr_lft then p := q.qarr_rgt
  stavar l_prv: addr
  var p_prv: ptr (l_prv) = p - sizeof<a>
  prval pf = __assert () where {
    extern prfun __assert (): DEQUEptrprv_p (a, lft, rgt, l, l_prv)
  } // end of [prval]
in
  (pf | p_prv)
end // end of [DEQUEptrprv]

(* ****** ****** *)

absprop
DEQUEptrnxt_p (
  a:viewt@ype, lft:addr, rgt:addr, l:addr, l_nxt:addr
) // end of [DEQUEptrnxt_p]

extern
fun{a:viewt@ype}
DEQUEptrnxt
  {m,n:nat} {lft,rgt,l_beg,l_end:addr} {l:addr}
  (q: &DEQUE_vt (a, m, n, lft, rgt, l_beg, l_end), p: ptr l)
  :<> [l_nxt:addr] (DEQUEptrnxt_p (a, lft, rgt, l, l_nxt) | ptr l_nxt)
// end of [DEQUEptrnxt_p]

implement{a}
DEQUEptrnxt {m,n}
  {lft,rgt,l_beg,l_end} {l} (q, p) = let
  var p_nxt: Ptr = p + sizeof<a>
  val () = if p_nxt >= q.qarr_rgt then p_nxt := q.qarr_lft
  stavar l_nxt: addr
  val _ = p_nxt: ptr l_nxt
  prval pf = __assert () where {
    extern prfun __assert (): DEQUEptrnxt_p (a, lft, rgt, l, l_nxt)
  } // end of [prval]
in
  (pf | p_nxt)
end // end of [DEQUEptrnxt]

(* ****** ****** *)

assume DEQUE (
  a:viewt@ype, m:int, n:int
) = [
  lft,rgt,l_beg,l_end:addr
] DEQUE_vt (
  a, m, n, lft, rgt, l_beg, l_end
) // end of [DEQUE]

(* ****** ****** *)

implement deque_cap (q) = q.cap
implement deque_size (q) = q.nitm

implement deque_is_empty (q) = (q.nitm <= 0)
implement deque_isnot_empty (q) = (q.nitm > 0)

implement deque_is_full (q) = (q.cap <= q.nitm)
implement deque_isnot_full (q) = (q.cap > q.nitm)

(* ****** ****** *)

implement{a}
deque_initialize {m} (
  pfgc, pfarr | q, m, parr
) =
  deque_initialize_tsz {a} {m} (pfgc, pfarr | q, m, parr, sizeof<a>)
// end of [deque_initialize]

//
// HX-2010-03-29:
// the function is given the external name:
// atslib_lindeque_arr_deque_initialize_tsz
//
implement
deque_initialize_tsz
  {a} {m} (
  pfgc, pfarr | q, m, parr, tsz
) = () where {
  prval () = __assert (q) where {
    extern prfun __assert (q: &DEQUE0 a >> DEQUE0_vt a):<> void
  } // end of [val]
  val () = q.cap := m
  val () = q.nitm := (size1_of_int1)0
  val [ofs:int] (pfmul | ofs) = mul2_size1_size1 (m, tsz)
  val () = q.qarr_lft := parr
  val () = q.qarr_rgt := parr + ofs
  val () = q.qarr_beg := parr
  val () = q.qarr_end := parr
  prval pfqarr = DEQUEarr_v_encode {a} (pfmul, pfarr)
  prval () = q.pfqarr := pfqarr
  prval () = q.pfqarr_gc := pfgc
} // end of [deque_initialize_tsz]

(* ****** ****** *)
//
// HX-2010-03-29:
// the function is given the external name:
// atslib_ngc_deque_arr_deque_uninitialize
//
implement
deque_uninitialize
  {a} {m,n} (q) = let
  prval pfgc = q.pfqarr_gc
  prval pfqarr = DEQUEarr_v_clear (q.pfqarr)
  prval pfarr = DEQUEarr_v_decode (pfqarr)
  val parr = q.qarr_lft
  prval () = __assert (q) where {
    extern prfun __assert (q: &DEQUE0_vt a >> DEQUE0 a):<> void
  } // end of [val]
in
  (pfgc, pfarr | parr)
end // end of [deque_uninitialize]

implement
deque_uninitialize_vt
  {a} {m} (q) = let
  prval pfgc = q.pfqarr_gc
  prval pfarr = DEQUEarr_v_decode (q.pfqarr)
  val parr = q.qarr_lft
  prval () = __assert (q) where {
    extern prfun __assert (q: &DEQUE0_vt a >> DEQUE0 a):<> void
  } // end of [val]
in
  (pfgc, pfarr | parr)
end // end of [deque_uninitialize_vt]

(* ****** ****** *)

extern
prfun DEQUEarr_insert_beg
  {a:viewt@ype} {m,n:nat | m > n}
  {lft,rgt,l_beg,l_end:addr} {l1_beg:addr} (
  pf1: DEQUEarr_v (a, m, n, lft, rgt, l_beg, l_end)
, pf2: DEQUEptrprv_p (a, lft, rgt, l_beg, l1_beg)
) : (
  a? @ l1_beg
, a @ l1_beg -<lin> DEQUEarr_v (a, m, n+1, lft, rgt, l1_beg, l_end)
) // end of [DEQUEarr_insert_beg]

implement{a}
deque_insert_beg (q, x) = let
  val p_beg = q.qarr_beg
  val (pf_prv | p1_beg) = DEQUEptrprv (q, p_beg)
  prval (pf_at, fpf) = DEQUEarr_insert_beg {a} (q.pfqarr, pf_prv)
  val () = !p1_beg := x
  val () = q.nitm := q.nitm + 1
  val () = q.qarr_beg := p1_beg
  prval () = q.pfqarr := fpf (pf_at)
in
 // nothing
end // end of [deque_insert_beg]

(* ****** ****** *)

extern
prfun DEQUEarr_insert_end
  {a:viewt@ype} {m,n:nat | m > n}
  {lft,rgt,l_beg,l_end:addr} {l1_end:addr} (
  pf1: DEQUEarr_v (a, m, n, lft, rgt, l_beg, l_end)
, pf2: DEQUEptrnxt_p (a, lft, rgt, l_end, l1_end)
) : (
  a? @ l_end
, a @ l_end -<lin> DEQUEarr_v (a, m, n+1, lft, rgt, l_beg, l1_end)
) // end of [DEQUEarr_insert_end]

implement{a}
deque_insert_end (q, x) = let
  val p_end = q.qarr_end
  val (pf_nxt | p1_end) = DEQUEptrnxt (q, p_end)
  prval (pf_at, fpf) = DEQUEarr_insert_end {a} (q.pfqarr, pf_nxt)
  val () = !p_end := x
  val () = q.nitm := q.nitm + 1
  val () = q.qarr_end := p1_end
  prval () = q.pfqarr := fpf (pf_at)
in
 // nothing
end // end of [deque_insert_end]

implement{a}
deque_insert_end_many (q, k, xs) =
  deque_insert_end_many_tsz {a} (q, k, xs, sizeof<a>)
// end of [deque_insert_end_many]

(* ****** ****** *)

extern
prfun DEQUEarr_remove_beg
  {a:viewt@ype} {m,n:nat | n > 0}
  {lft,rgt,l_beg,l_end:addr} {l1_beg:addr} (
  pf1: DEQUEarr_v (a, m, n, lft, rgt, l_beg, l_end)
, pf2: DEQUEptrnxt_p (a, lft, rgt, l_beg, l1_beg)
) : (
  a @ l_beg
, a? @ l_beg -<lin> DEQUEarr_v (a, m, n-1, lft, rgt, l1_beg, l_end)
) // end of [DEQUEarr_remove_beg]

implement{a}
deque_remove_beg (q) = x where {
  val p_beg = q.qarr_beg
  val (pf_nxt | p1_beg) = DEQUEptrnxt (q, p_beg)
  prval (pf_at, fpf) = DEQUEarr_remove_beg {a} (q.pfqarr, pf_nxt)
  val x = !p_beg
  val () = q.nitm := q.nitm - 1
  val () = q.qarr_beg := p1_beg
  prval () = q.pfqarr := fpf (pf_at)
} // end of [deque_remove_beg]

implement{a}
deque_remove_beg_many (q, k, xs) =
  deque_remove_beg_many_tsz {a} (q, k, xs, sizeof<a>)
// end of [deque_remove_beg_many]

(* ****** ****** *)

extern
prfun DEQUEarr_remove_end
  {a:viewt@ype} {m,n:nat | n > 0}
  {lft,rgt,l_beg,l_end:addr} {l1_end:addr} (
  pf1: DEQUEarr_v (a, m, n, lft, rgt, l_beg, l_end)
, pf2: DEQUEptrprv_p (a, lft, rgt, l_end, l1_end)
) : (
  a @ l1_end
, a? @ l1_end -<lin> DEQUEarr_v (a, m, n-1, lft, rgt, l_beg, l1_end)
) // end of [DEQUEarr_remove_end]

(* ****** ****** *)

implement{a}
deque_update_capacity (
  pfgc2, pfarr2 | q, m2, xs
) =
  deque_update_capacity_tsz {a} (pfgc2, pfarr2 | q, m2, xs, sizeof<a>)
// end of [deque_update_capacity]

(* ****** ****** *)

(* end of [lindeque_arr.dats] *)
