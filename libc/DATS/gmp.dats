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
 * the  terms of the  GNU General Public License as published by the Free
 * Software Foundation; either version 2.1, or (at your option) any later
 * version.
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

#define ATS_DYNLOADFLAG 0 // there is no need for dynloading at run-time

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

%{

ats_void_type
atslib_mpz_out_str_exn (
  ats_ptr_type file
, ats_int_type base
, const ats_mpz_ptr_type x
) {
  size_t n = mpz_out_str((FILE*)file, base, (mpz_ptr)x) ;
  if (n == 0) {
    ats_exit_errmsg (1, "exit(ATS): [mpz_out_str] failed.\n") ;
  } // end of [if]
  return ;
} // end of [atslib_mpz_out_str_exn]

ats_void_type
atslib_mpz_inp_str_exn (
  ats_mpz_ptr_type x
, ats_ptr_type file
, ats_int_type base
) {
  size_t n = mpz_inp_str(x, (FILE*)file, base) ;
  if (n == 0) {
    ats_exit_errmsg (1, "exit(ATS): [mpz_inp_str] failed.\n") ;
  } // end of [if]
  return ;
} // end of [atslib_mpz_inp_str_exn]

%} // end of [%{]

(* ****** ****** *)

implement print_mpz (x) = print_mac (fprint1_mpz, x)
implement prerr_mpz (x) = prerr_mac (fprint1_mpz, x)

(* ****** ****** *)

%{

ats_void_type
atslib_mpf_out_str_exn (
  ats_ptr_type file
, ats_int_type base
, ats_size_type ndigit
, const ats_mpf_ptr_type x
) {
  size_t n = mpf_out_str((FILE*)file, base, ndigit, (mpf_ptr)x) ;
  if (n == 0) {
    ats_exit_errmsg (1, "exit(ATS): [mpf_out_str] failed.\n") ;
  } // end of [if]
  return ;
} // end of [atslib_mpf_out_str_exn]

ats_void_type
atslib_mpf_inp_str_exn (
  ats_mpf_ptr_type x
, ats_ptr_type file
, ats_int_type base
) {
  size_t n = mpf_inp_str(x, (FILE*)file, base) ;
  if (n == 0) {
    ats_exit_errmsg (1, "exit(ATS): [mpf_inp_str] failed.\n") ;
  } // end of [if]
  return ;
} // end of [atslib_mpf_inp_str_exn]

%} // end of [%{]

(* ****** ****** *)

(* end of [gmp.dats] *)
