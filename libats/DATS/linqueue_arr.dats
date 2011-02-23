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
** An array-based queue implementation
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

staload "libats/SATS/linqueue_arr.sats"

(* ****** ****** *)

absview QUEUEarr_v (
  a:viewt@ype+
, m:int, n:int, l_beg:addr, l_end:addr, l_fst:addr, l_lst:addr
) // end of [QUEUEarr_v]

extern prfun
QUEUEarr_v_encode {a:viewt@ype}
{m:nat} {l_beg:addr} {ofs:int} (
  pfmul: MUL (m, sizeof a, ofs), pfarr: array_v (a?, m, l_beg)
) :<prf> QUEUEarr_v (a, m, 0, l_beg, l_beg+ofs, l_beg, l_beg)
// end of [QUEUEarr_v_encode]

extern prfun
QUEUEarr_v_decode {a:viewt@ype}
{m:nat} {l_beg,l_end,l_fst,l_lst:addr} (
  pf: QUEUEarr_v (a, m, 0, l_beg, l_end, l_fst, l_lst)
) :<prf> array_v (a?, m, l_beg) // end of [QUEUEarr_v_decode]

extern prfun
QUEUEarr_v_clear {a:t@ype}
{m,n:nat} {l_beg,l_end,l_fst,l_lst:addr} (
  pf: QUEUEarr_v (a, m, n, l_beg, l_end, l_fst, l_lst)
) :<prf> QUEUEarr_v (a, m, 0, l_beg, l_end, l_beg, l_beg)
// end of [QUEUEarr_v_clear]

(* ****** ****** *)

viewtypedef QUEUE_vt (
  a:viewt@ype, m:int, n:int
, l_beg:addr, l_end:addr, l_fst:addr, l_lst:addr
) = $extype_struct "atslib_linqueue_arr_QUEUE" of {
  cap= size_t m
, nitm= size_t n
, qarr_beg = ptr l_beg
, qarr_end = ptr l_end
, qarr_fst= ptr l_fst
, qarr_lst= ptr l_lst
, pfqarr= QUEUEarr_v (a, m, n, l_beg, l_end, l_fst, l_lst)
, pfqarr_gc= free_gc_v (a, m, l_beg)
} // end of [QUEUE_vt]

typedef QUEUE0_vt
  (a:viewt@ype) = QUEUE_vt (a, 0, 0, null, null, null, null)?
// end of [QUEUE0_vt]

(* ****** ****** *)

absview QUEUEptrnxt_p
  (a:viewt@ype, l_beg:addr, l_end:addr, l:addr, l_nxt:addr)
// end of [QUEUEptrnxt_p]

extern
fun{a:viewt@ype}
QUEUEptrnxt
  {m,n:nat} {l_beg,l_end,l_fst,l_lst:addr} {l:addr}
  (q: &QUEUE_vt (a, m, n, l_beg, l_end, l_fst, l_lst), p: ptr l)
  :<> [l_nxt:addr] (QUEUEptrnxt_p (a, l_beg, l_end, l, l_nxt) | ptr l_nxt)
// end of [QUEUEptrnxt_p]

implement{a}
QUEUEptrnxt {m,n}
  {l_beg,l_end,l_fst,l_lst} {l} (q, p) = let
  var p_nxt: Ptr = p + sizeof<a>
  val () = if p_nxt >= q.qarr_end then p_nxt := q.qarr_beg
  stavar l_nxt: addr
  val _ = p_nxt: ptr l_nxt
  prval pf = __assert () where {
    extern prfun __assert (): QUEUEptrnxt_p (a, l_beg, l_end, l, l_nxt)
  } // end of [prval]
in
  (pf | p_nxt)
end // end of [QUEUEptrnxt]

(* ****** ****** *)

extern
prfun QUEUEarr_takeout_fst
   {a:viewt@ype} {m,n:nat | n > 0}
   {l_beg,l_end,l_fst,l_lst:addr} {l_fst1:addr} (
    pf1: QUEUEarr_v (a, m, n, l_beg, l_end, l_fst, l_lst)
  , pf2: QUEUEptrnxt_p (a, l_beg, l_end, l_fst, l_fst1)
  ) : (a @ l_fst, a? @ l_fst -<lin> QUEUEarr_v (a, m, n-1, l_beg, l_end, l_fst1, l_lst))
// end of [QUEUEarr_takeout_fst]

extern
prfun QUEUEarr_takeout_lst
   {a:viewt@ype} {m,n:nat | m > n}
   {l_beg,l_end,l_fst,l_lst:addr} {l_lst1:addr} (
    pf1: QUEUEarr_v (a, m, n, l_beg, l_end, l_fst, l_lst)
  , pf2: QUEUEptrnxt_p (a, l_beg, l_end, l_lst, l_lst1)
  ) : (a? @ l_lst, a @ l_lst -<lin> QUEUEarr_v (a, m, n+1, l_beg, l_end, l_fst, l_lst1))
// end of [QUEUEarr_takeout_fst]

(* ****** ****** *)

assume QUEUE (a:viewt@ype, m:int, n:int) =
  [l_beg,l_end,l_fst,l_lst:addr] QUEUE_vt (a, m, n, l_beg, l_end, l_fst, l_lst)
// end of [QUEUE]

(* ****** ****** *)

implement queue_cap (q) = q.cap
implement queue_size (q) = q.nitm

implement queue_is_empty (q) = (q.nitm <= 0)
implement queue_isnot_empty (q) = (q.nitm > 0)

implement queue_is_full (q) = (q.cap <= q.nitm)
implement queue_isnot_full (q) = (q.cap > q.nitm)

(* ****** ****** *)

implement{a}
queue_initialize {m} (q, m) = queue_initialize_tsz {a} {m} (q, m, sizeof<a>)
// end of [queue_initialize]

//
// HX-2010-03-29:
// the function is given the external name:
// atslib_linqueue_arr_queue_initialize_tsz
//
implement
queue_initialize_tsz
  {a} {m} (q, m, tsz) = () where {
  prval () = __assert (q) where {
    extern prfun __assert (q: &QUEUE0 a >> QUEUE0_vt a):<> void
  } // end of [val]
  val () = q.cap := m
  val () = q.nitm := (size1_of_int1)0
  val [l_beg:addr] (pfarr_gc, pfarr | p_beg) = array_ptr_alloc_tsz {a} (m, tsz)
  val [ofs:int] (pfmul | ofs) = mul2_size1_size1 (m, tsz)
  val () = q.qarr_beg := p_beg
  val () = q.qarr_end := p_beg + ofs
  val () = q.qarr_fst := p_beg
  val () = q.qarr_lst := p_beg
  prval pfqarr = QUEUEarr_v_encode {a} (pfmul, pfarr)
  prval () = q.pfqarr := pfqarr
  prval () = q.pfqarr_gc := pfarr_gc
} // end of [queue_initialize_tsz]

(* ****** ****** *)

implement{a}
queue_insert (q, x) = let
  val p_lst = q.qarr_lst
  val (pf_nxt | p_lst1) = QUEUEptrnxt (q, p_lst)
  prval (pf_at, fpf) = QUEUEarr_takeout_lst {a} (q.pfqarr, pf_nxt)
  val () = !p_lst := x
  val () = q.nitm := q.nitm + 1
  val () = q.qarr_lst := p_lst1
  prval () = q.pfqarr := fpf (pf_at)
in
 // nothing
end // end of [queue_insert]

(* ****** ****** *)

implement{a}
queue_remove (q) = x where {
  val p_fst = q.qarr_fst
  val (pf_nxt | p_fst1) = QUEUEptrnxt (q, p_fst)
  prval (pf_at, fpf) = QUEUEarr_takeout_fst {a} (q.pfqarr, pf_nxt)
  val x = !p_fst
  val () = q.nitm := q.nitm - 1
  val () = q.qarr_fst := p_fst1
  prval () = q.pfqarr := fpf (pf_at)
} // end of [queue_remove]

(* ****** ****** *)

//
// HX-2010-03-29:
// the function is given the external name:
// atslib_linqueue_arr_queue_uninitialize
//
implement
queue_uninitialize
  {a} {m,n} (q) = () where {
  prval pfqarr = QUEUEarr_v_clear (q.pfqarr)
  prval pfarr = QUEUEarr_v_decode (pfqarr)
  val () = array_ptr_free {a} (q.pfqarr_gc, pfarr | q.qarr_beg)
  prval () = __assert (q) where {
    extern prfun __assert (q: &QUEUE0_vt a >> QUEUE0 a):<> void
  } // end of [val]
} // end of [queue_uninitialize]

implement
queue_uninitialize_vt
  {a} {m} (q) = () where {
  prval pfarr = QUEUEarr_v_decode (q.pfqarr)
  val () = array_ptr_free {a} (q.pfqarr_gc, pfarr | q.qarr_beg)
  prval () = __assert (q) where {
    extern prfun __assert (q: &QUEUE0_vt a >> QUEUE0 a):<> void
  } // end of [val]
} // end of [queue_uninitialize_vt]

(* ****** ****** *)

(* end of [linqueue_arr.dats] *)
