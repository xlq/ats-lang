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
** A array-based stack implementation
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

staload "libats/SATS/linstack_arr.sats"

(* ****** ****** *)

absview STACKarr_v
  (a:viewt@ype+, m:int, n:int, l_beg:addr, l_cur:addr)
// end of [STACKarr_v]

extern prfun
STACKarr_v_encode
  {a:viewt@ype} {m:int} {l_beg:addr} (pfarr: array_v (a?, m, l_beg))
  :<prf> STACKarr_v (a, m, 0, l_beg, l_beg)
// end of [STACKarr_v_encode]

extern prfun
STACKarr_v_decode
  {a:viewt@ype} {m:int} {l_beg,l_cur:addr}
  (pf: STACKarr_v (a, m, 0, l_beg, l_cur)):<prf> array_v (a?, m, l_beg)
// end of [STACKarr_v_decode]

extern prfun
STACKarr_v_clear {a:t@ype}
  {m:int} {n1,n2:nat | n1 >= n2} {l_beg,l_cur:addr} {ofs:int} (
  pfmul: MUL (n2, sizeof a, ofs), pfarr: STACKarr_v (a, m, n1, l_beg, l_cur)
) :<prf> STACKarr_v (a, m, n2, l_beg, l_beg+ofs)
// end of [STACKarr_v_clear]

(* ****** ****** *)

viewtypedef STACK_vt (
  a:viewt@ype, m:int, n:int, l_beg:addr, l_cur:addr
) = $extype_struct "atslib_linstack_arr_STACK" of {
  cap= size_t m
, nitm= size_t n // = (l_beg - l_cur) / sizeof(a)
, sarr_beg = ptr l_beg // this is definitely needed if GC is involved
, sarr_cur = ptr l_cur
, pfsarr= STACKarr_v (a, m, n, l_beg, l_cur)
, pfsarr_gc= free_gc_v (a, m, l_beg)
} // end of [STACK_vt]

typedef STACK0_vt
  (a:viewt@ype) = STACK_vt (a, 0, 0, null, null)?
// end of [STACK0_vt]

(* ****** ****** *)

extern
prfun STACKarr_takeout_prv
   {a:viewt@ype} {m,n:nat | n > 0}
   {l_beg:addr} {l_prv:addr} (
    pf1: STACKarr_v (a, m, n, l_beg, l_prv+sizeof(a))
  ) : (a @ l_prv, a? @ l_prv -<lin> STACKarr_v (a, m, n-1, l_beg, l_prv))
// end of [STACKarr_takeout_fst]

extern
prfun STACKarr_takeout_cur
   {a:viewt@ype} {m,n:nat | m > n}
   {l_beg:addr} {l_cur:addr} (
    pf1: STACKarr_v (a, m, n, l_beg, l_cur)
  ) : (a? @ l_cur, a @ l_cur -<lin> STACKarr_v (a, m, n+1, l_beg, l_cur+sizeof a))
// end of [STACKarr_takeout_fst]

(* ****** ****** *)

assume STACK (a:viewt@ype, m:int, n:int) =
  [l_beg,l_cur:addr] STACK_vt (a, m, n, l_beg, l_cur)
// end of [STACK]

(* ****** ****** *)

implement stack_get_cap (s) = s.cap
implement stack_get_size (s) = s.nitm

implement stack_is_empty (s) = (s.nitm = 0)
implement stack_isnot_empty (s) = (s.nitm > 0)

implement stack_is_full (s) = (s.cap = s.nitm)
implement stack_isnot_full (s) = (s.cap > s.nitm)

(* ****** ****** *)

implement{a}
stack_initialize {m} (s, m) = () where {
  prval () = __assert (s) where {
    extern prfun __assert (s: &STACK0 a >> STACK0_vt a):<> void
  } // end of [val]
  val () = s.cap := m
  val () = s.nitm := (size1_of_int1)0
  val tsz = sizeof<a>
  val [l_beg:addr] (pfarr_gc, pfarr | p_beg) = array_ptr_alloc_tsz {a} (m, tsz)
  val () = s.sarr_beg := p_beg
  val () = s.sarr_cur := p_beg
  prval pfsarr = STACKarr_v_encode {a} (pfarr)
  prval () = s.pfsarr := pfsarr
  prval () = s.pfsarr_gc := pfarr_gc
} // end of [stack_initialize]

(* ****** ****** *)

implement{a}
stack_insert (s, x) = let
  val p_cur = s.sarr_cur
  prval (pf_at, fpf) = STACKarr_takeout_cur {a} (s.pfsarr)
  val () = !p_cur := x
  val () = s.nitm := s.nitm + 1
  val () = s.sarr_cur := p_cur + sizeof<a>
  prval () = s.pfsarr := fpf (pf_at)
in
 // nothing
end // end of [stack_insert]

(* ****** ****** *)

implement{a}
stack_remove (s) = x where {
  val p_cur = s.sarr_cur
  stavar l_prv: addr
  val p_prv = (p_cur - sizeof<a>): ptr l_prv
  prval (pf_at, fpf) = STACKarr_takeout_prv {a} {..} {..} {l_prv} (s.pfsarr)
  val x = !p_prv
  val () = s.nitm := s.nitm - 1
  val () = s.sarr_cur := p_prv
  prval () = s.pfsarr := fpf (pf_at)
} // end of [stack_remove]

(* ****** ****** *)

implement{a}
stack_clear {m} {n1,n2} (s, n2) = () where {
  val (pfmul | ofs) = mul2_size1_size1 (n2, sizeof<a>)
  prval pfsarr = STACKarr_v_clear {a} {m} {n1,n2} (pfmul, s.pfsarr)
  val () = s.nitm := n2
  val () = s.sarr_cur := s.sarr_beg + ofs
  prval () = s.pfsarr := pfsarr
} // end of [stack_clear]

(* ****** ****** *)

implement
stack_uninitialize
  {a} {m,n} (s) = () where {
  prval pfmul = mul_make {0,sizeof(a)} ()
  prval pfsarr = STACKarr_v_clear {a} {m} {n,0} (pfmul, s.pfsarr)
  prval pfarr = STACKarr_v_decode (pfsarr)
  val () = array_ptr_free (s.pfsarr_gc, pfarr | s.sarr_beg)
  prval () = __assert (s) where {
    extern prfun __assert (s: &STACK0_vt a >> STACK0 a):<> void
  } // end of [val]
} // end of [stack_uninitialize]

implement
stack_uninitialize_vt
  {a} {m} (s) = () where {
  prval pfarr = STACKarr_v_decode (s.pfsarr)
  val () = array_ptr_free (s.pfsarr_gc, pfarr | s.sarr_beg)
  prval () = __assert (s) where {
    extern prfun __assert (s: &STACK0_vt a >> STACK0 a):<> void
  } // end of [val]
} // end of [stack_uninitialize_vt]

(* ****** ****** *)

(* end of [linstack_arr.dats] *)
