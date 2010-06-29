(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October 2007

(* ****** ****** *)

%{^

static // no need for marking the variable as it
ats_int_type the_debug_flag = 0 ; // contains no pointer

ats_int_type
atsopt_debug_flag_get () { return the_debug_flag ; }

ats_void_type
atsopt_debug_flag_set
  (ats_int_type i) { the_debug_flag = i ; return ; }
// end of [atsopt_debug_flag_set]

ats_void_type
atsopt_debug_prerrf (
  ats_ptr_type fmt, ...
) {
  int n ;
  va_list ap ;
//
  if (!the_debug_flag) return ;
//
  va_start(ap, fmt) ;
  n = vfprintf(stderr, (char*)fmt, ap) ;
  va_end(ap) ;
  if (n < 0) {
    ats_exit_errmsg(n, "[prerrf] failed\n") ;
  } // end of [if]
//
  return ;
} // end of [atsopt_debug_prerrf]

ats_void_type
atsopt_debug_printf (
  ats_ptr_type fmt, ...
) {
  int n ;
  va_list ap ;
//
  if (!the_debug_flag) return ;
//
  va_start(ap, fmt) ;
  n = vfprintf(stdout, (char*)fmt, ap) ;
  va_end(ap) ;
  if (n < 0) {
    ats_exit_errmsg(n, "[printf] failed\n") ;
  } // end of [if]
//
  return ;
} // end of [atsopt_debug_printf]

%} // end of [%{^]

(* ****** ****** *)

(* end of [ats_debug.dats] *)
