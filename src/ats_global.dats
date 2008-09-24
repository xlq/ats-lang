(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS/Anairiats - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
 * Free Software Foundation; either version 3, or (at  your  option)  any
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

// Time: July 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

(* ats_global: handling some global variables *)

(* ****** ****** *)

val () = ats_global_initialize () where {
  extern fun ats_global_initialize (): void = "ats_global_initialize"
}

(* ****** ****** *)

%{$

static ats_int_type the_ats_dynloadflag = 0 ;

ats_int_type
ats_global_ats_dynloadflag_get () {
  return the_ats_dynloadflag ;
}

ats_void_type
ats_global_ats_dynloadflag_set (ats_int_type flag) {
  the_ats_dynloadflag = flag ; return ;
}

/* ****** ****** */

static ats_ptr_type the_ats_dynloadfuname = (ats_ptr_type)0 ;

ats_ptr_type
ats_global_ats_dynloadfuname_get () {
  return the_ats_dynloadfuname ;
}

ats_void_type
ats_global_ats_dynloadfuname_set (ats_ptr_type name) {
  the_ats_dynloadfuname = name ; return ;
}

%}

(* ****** ****** *)


%{$

static ats_ptr_type
the_ats_function_name_prefix = (ats_ptr_type)0 ;

ats_ptr_type
ats_global_ats_function_name_prefix_get () {
  return the_ats_function_name_prefix ;
}

ats_void_type
ats_global_ats_function_name_prefix_set (ats_ptr_type prfx) {
  the_ats_function_name_prefix = prfx ; return ;
}

%}

(* ****** ****** *)

%{$

static ats_int_type the_ats_depgenflag = 0 ;

ats_int_type
ats_global_ats_depgenflag_get () {
  return the_ats_depgenflag ;
}

ats_void_type
ats_global_ats_depgenflag_set (ats_int_type flag) {
  the_ats_depgenflag = flag ; return ;
}

%}

(* ****** ****** *)

%{$

ats_void_type ats_global_initialize () {
  ATS_GC_MARKROOT (&the_ats_dynloadfuname, sizeof(ats_ptr_type)) ;
  ATS_GC_MARKROOT (&the_ats_function_name_prefix, sizeof(ats_ptr_type)) ;
  return ;
}

%}

(* ****** ****** *)

(* end of [ats_counter.dats] *)
