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
** An array-based queue implementation
** Author: hwxi AT cs DOT bu DOT edu
** Time: March, 2011
*)

(* ****** ****** *)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no static loading at run-time

(* ****** ****** *)

staload DQ = "libats/ngc/SATS/deque_arr.sats"

(* ****** ****** *)

staload "libats/SATS/linqueue_arr.sats"

(* ****** ****** *)

assume QUEUE (
  a:viewt@ype, m:int, n:int
) = $DQ.DEQUE (a, m, n)

(* ****** ****** *)

implement queue_cap (q) = $DQ.deque_cap (q)
implement queue_size (q) = $DQ.deque_size (q)

implement queue_is_empty (q) = $DQ.deque_is_empty (q)
implement queue_isnot_empty (q) = $DQ.deque_isnot_empty (q)

implement queue_is_full (q) = $DQ.deque_is_full (q)
implement queue_isnot_full (q) = $DQ.deque_isnot_full (q)

(* ****** ****** *)

implement{a}
queue_initialize
  {m} (q, m) = let
  val (pfgc, pfarr | parr) = array_ptr_alloc<a> (m)
in
  $DQ.deque_initialize<a> {m} (pfgc, pfarr | q, m, parr)
end // end of [queue_initialize]

(* ****** ****** *)
//
// HX-2010-03-29:
// the function is given the external name:
// atslib_linqueue_arr_queue_uninitialize
//
implement
queue_uninitialize
  {a} {m,n} (q) = () where {
  val (pfgc, pfarr | parr) = $DQ.deque_uninitialize (q)
  val () = array_ptr_free (pfgc, pfarr | parr)
} // end of [queue_uninitialize]

implement
queue_uninitialize_vt
  {a} {m} (q) = () where {
  val (pfgc, pfarr | parr) = $DQ.deque_uninitialize_vt (q)
  val () = array_ptr_free (pfgc, pfarr | parr)
} // end of [queue_uninitialize_vt]

(* ****** ****** *)

implement{a}
queue_insert (q, x) =
  $DQ.deque_insert_end (q, x)
// end of [queue_insert]

implement{a}
queue_remove (q) = $DQ.deque_remove_beg (q)

(* ****** ****** *)

(* end of [linqueue_arr.dats] *)
