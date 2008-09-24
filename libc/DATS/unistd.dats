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

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

%{^

#include <errno.h>
#include <unistd.h>

ats_int_type
atslib_fork_and_exec_and_wait (ats_clo_ptr_type f_child) {
  pid_t pid ;
  int status ;

  pid = fork () ;
  if (pid < 0) {
    ats_exit_errmsg (errno, "Exit: [fork] failed.\n") ;
  }
  if (pid > 0) { wait (&status) ; return status ; }
  /* this is the child */
  ((ats_void_type (*)(ats_clo_ptr_type))f_child->closure_fun)(f_child) ;
  exit (0) ;
}

#define __GETCWD_BUFSZ 64

ats_ptr_type atslib_getcwd () {
  char *buf, *res ;
  int sz = __GETCWD_BUFSZ ;

  buf = (char*)ats_malloc_gc(__GETCWD_BUFSZ) ;
  while (1) {
    res = getcwd (buf, sz) ;
    if (!res) {
      ats_free_gc (buf) ;
      sz = sz + sz ; buf = (char*)ats_malloc_gc (sz) ;
      continue ;
    }
    break ;
  }
  return buf ;
}

%}

(* ****** ****** *)

(* end of [unistd.dats] *)
