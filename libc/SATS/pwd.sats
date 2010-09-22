(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
**
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
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#
#include "libc/CATS/pwd.cats"
%} // end of [%{#]

(* ****** ****** *)

staload T = "libc/sys/SATS/types.sats"
typedef uid_t = $T.uid_t

(* ****** ****** *)

abst@ype passwd_t = $extype "ats_passwd_type"

(* ****** ****** *)

// HX: non-reentrant
fun getpwnam (nam: string):<!ref> [l:addr]
  (option_v ((passwd_t @ l, passwd_t @ l -<prf> void), l > null) | ptr l)
  = "#atslib_getpwnam"
// end of [getpwnam]

// HX: non-reentrant
fun getpwuid (uid: uid_t):<!ref> [l:addr]
  (option_v ((passwd_t @ l, passwd_t @ l -<prf> void), l > null) | ptr l)
  = "#atslib_getpwuid"
// end of [getpwuid]

(* ****** ****** *)

(* end of [pwd.sats] *)
