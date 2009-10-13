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
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

staload "libc/SATS/random.sats"

(* ****** ****** *)

%{^

/* ****** ****** */

ats_void_type // [n] is assumed to be positive!
atslib_randint_r (
  ats_ref_type buf, ats_int_type n, ats_ref_type i
) {
  ats_lint_type tmp ;
  atslib_lrand48_r ((ats_drand48_data_type*)buf, &tmp) ; // the return is 0
  *(ats_int_type*)i = tmp % n ;
  return ;
} /* end of [atslib_randint_r] */

%} // end of [%{^ ... %}]

(* ****** ****** *)

(* end of [random.dats] *)
