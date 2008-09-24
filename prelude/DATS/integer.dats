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

// some basic IO operations

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no initialization is needed

(* ****** ****** *)

%{$

// stringization

ats_ptr_type
atspre_tostring_llint (ats_llint_type i0) {
  int i, n ;
  char *res ;

  i = (i0 >= 0 ? i0 : -i0) ;
  for (n = 0; i > 0; i = i / 10) ++n ;
  if (i0 < 0) { ++n ; }

  res = ATS_MALLOC(n+1) ; res = res + n;

  *res = '\000' ; --res ;

  i = (i0 >= 0 ? i0 : -i0) ;
  for (n = 0; i > 0; i = i / 10) {
    *res = ('0' + i % 10) ; --res ;
  }

  if (i0 < 0) *res = '-' ;

  return res ;
}

/* ****** ****** */

static /* inline */
ats_ptr_type
atspre_tostring_ullint (ats_ullint_type i0) {
  int i, n ;
  char *res ;

  i = i0 ;
  for (n = 0; i > 0; i = i / 10) ++n ;

  res = ATS_MALLOC(n+1) ; res = res + n;
  *res = '\000' ; --res ;

  i = i0 ;
  for (n = 0; i > 0; i = i / 10) {
    *res = ('0' + i % 10) ; --res ;
  }

  return res ;
}

%}

(* ****** ****** *)

(* end of [integer.dats] *)
