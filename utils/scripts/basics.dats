(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
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

// Time: Summer 2007

(* Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

staload STDLIB = "libc/SATS/stdlib.sats"

(* ****** ****** *)

staload "top.sats"

(* ****** ****** *)

exception Fatal of string

local

#include "prelude/params_system.hats"

in

#if OPERATING_SYSTEM_IS_UNIX_LIKE #then

val dirsep: char = '/'

#endif

end

(* ****** ****** *)

implement atsopt_local = "bin/atsopt"
implement precats_local = "prelude/CATS/"
implement runtime_local = "ccomp/runtime/"

implement atslib_local = "ccomp/lib/"

implement atslib_output_local = "ccomp/lib/output/"

implement libats_local = "ccomp/lib/libats.a"

// multithreaded
implement libats_mt_local = "ccomp/lib/libats_mt.a"

(* ****** ****** *)

local

#define ATSHOME_var "ATSHOME"

in

fn ATSHOME_get (): String = let
  val ATSHOME_opt = $STDLIB.getenv_opt ATSHOME_var
in
  if stropt_is_some ATSHOME_opt then
    string1_of_string0 (stropt_unsome ATSHOME_opt)
  else begin
    prerr "The environment variable [";
    prerr ATSHOME_var;
    prerr "] is undefined!";
    prerr_newline ();
    $raise (Fatal "ATSHOME_get")
  end
end // end of [ATSHOME_get]

end // end of [local]

implement ATSHOME_dir = let
  val ATSHOME = ATSHOME_get ()
  val n = length ATSHOME
in
  if n > 0 then
    if string_get_char_at (ATSHOME, n-1) = dirsep then ATSHOME
    else ATSHOME + "/"
  else begin
    prerr "The variable [ATSHOME] is empty!\n" ;
    $raise (Fatal "ATSHOME")
  end
end // end of [ATSHOME]

implement ATSHOME_dir_append basename =
  ATSHOME_dir + (string1_of_string0 basename)

(* ****** ****** *)

implement basename_of_filename name = let
  val name = string1_of_string0 name
  val n = length name
  val i = string_index_of_char_from_right (name, dirsep)
in
  if (i >= 0) then
    let val () = assert_prerrf
      (i < n, "[basename_of(%s)] failed.\n", @(name))
    in
      string_make_substring (name, i+1, n-i-1)
    end
  else name
end // end of [basename_of_filename]

implement suffix_of_filename name = let
  val name = string1_of_string0 name
  val i = 1+string_index_of_char_from_right (name, '.')
in
  if i > 0 then
    let val n = length name in
      if i < n then
        stropt_some (string_make_substring (name, i, n-i))
      else stropt_none
    end
  else stropt_none
end // end of [suffix_of_filename]

implement filename_is_local name = let
   val name = string1_of_string0 name
in
   if string1_is_not_empty name then
     bool1_of_bool (name[0] <> dirsep)
   else true
end // end of [filename_is_local]

(* ****** ****** *)

implement atsopt_global = ATSHOME_dir_append atsopt_local
implement precats_global = ATSHOME_dir_append precats_local
implement runtime_global = ATSHOME_dir_append runtime_local

implement atslib_global = ATSHOME_dir_append atslib_local
implement atslib_output_global = ATSHOME_dir_append atslib_output_local
implement libats_global = ATSHOME_dir_append libats_local
implement libats_mt_global = ATSHOME_dir_append libats_mt_local

(* ****** ****** *)

#define nil STRLSTnil
#define :: STRLSTcons

implement strlst_nil () = STRLSTnil ()
implement strlst_is_nil (ss) =
  case+ ss of nil () => true | _ :: _ => false

implement strlst_head_get (ss) = let val s :: _ = ss in s end
implement strlst_tail_get (ss) = let val _ :: ss = ss in ss end

implement strlst_length {n} ss = let
  fun aux {i,j:nat | i+j == n} .<i>.
    (ss: strlst i, res: int j): int n =
    case+ ss of nil () => res | _ :: ss => aux (ss, 1+res)
in
  aux (ss, 0)
end // end of [strlst_length]

implement strlst_reverse {n} ss = let
  fun aux {i,j:nat | i+j == n} .<i>.
    (ss: strlst i, res: strlst j): strlst n =
    case+ ss of nil () => res | s :: ss => aux (ss, s :: res)
in
   aux (ss, nil ())
end // end of [strlst_reverse]

(* ****** ****** *)

%{^

#include <errno.h>
#include <sys/stat.h>
#include <unistd.h>

/* ****** ****** */

#include "libc/CATS/stdlib.cats"

/* ****** ****** */

ats_void_type // also defined in [prelude/DATS/basics.dats]
ats_exit(const ats_int_type n) { exit(n) ; return ; }

ats_void_type // also defined in [prelude/DATS/basics.dats]
ats_exit_errmsg
  (const ats_int_type n, const ats_ptr_type errmsg)
{
  fprintf(stderr, "%s", (char *)errmsg) ; exit(n) ; return ;
}

/* ****** ****** */

ats_void_type // also defined in [prelude/DATS/printf.dats]
atspre_exit_prerrf
  (const ats_int_type n, const ats_ptr_type fmt, ...)
{
  va_list ap ;
  va_start(ap, fmt) ; vfprintf(stderr, (char *)fmt, ap) ; va_end(ap) ;
  exit (n) ;
}

//

ats_void_type // also defined in [prelude/DATS/printf.dats]
atspre_assert_prerrf
  (ats_bool_type assertion, ats_ptr_type fmt, ...)
{
  int n ;
  va_list ap ;

  if (!assertion) {
    va_start(ap, fmt) ;
    n = vfprintf(stderr, (char *)fmt, ap) ;
    va_end(ap) ;
    if (n < 0) { ats_exit_errmsg
      (n, "exit(ATS): [atspre_assert_prerrf: prerrf] failed\n") ;
    } else { ats_exit_errmsg
      (1, "exit(ATS): [atspre_assert_prerrf: assert] failed\n") ;
    } /* end of [if] */
  } /* end of [if] */

  return ;
} /* atspre_assert_prerrf */

//

static // also defined in [prelude/DATS/printf.dats]
ats_ptr_type __tostringf_size
  (const ats_int_type guess, const ats_ptr_type fmt, va_list ap)
{
  int n, sz ; char *res ;

  sz = guess ;
  res = ats_malloc_gc (sz) ;
  while (1) {
    n = vsnprintf (res, sz, (char *)fmt, ap) ;
    if (n >= 0) {
      if (n < sz) { return res ; }
      sz = n+1 ; /* exact size */
      ats_free_gc (res) ;
      res = ats_malloc_gc (sz) ;
      continue ;
    }
    return ((ats_ptr_type)0) ;
  }
} // end of [__tostringf_size]

//

ats_ptr_type // also defined in [prelude/DATS/printf.dats]
atspre_tostringf_size
  (const ats_int_type guess, const ats_ptr_type fmt, ...)
{
  char *res ;
  va_list ap ;

  va_start(ap, fmt);
  res = (char *)__tostringf_size (guess, fmt, ap);
  va_end(ap);
  if (!res) { ats_exit_errmsg
    (1, "exit(ATS): [ats_tostringf_size] failed.\n") ;
  }
  return res ;
} // end of [atspre_tostringf_size]

/* ****** ****** */

// also defined in [prelude/DATS/string.dats]

ats_ptr_type
atspre_string_make_substring
  (const ats_ptr_type src0, const ats_int_type start, const ats_int_type len)
{
  char *des, *src ;
  des = ATS_MALLOC(len+1) ;
  src = ((char*)src0) + start ;
  memcpy(des, src, len) ; des[len] = '\000' ;
  return des ;
} /* atspre_string_make_substring */

/* ****** ****** */

extern ats_ptr_type atsopt_global ;

ats_bool_type file_is_exec (ats_ptr_type name) {
  struct stat buf ;
  int ret = stat (name, &buf) ;

  if (ret < 0) { atspre_exit_prerrf
    (errno, "exit(ATS): File [%s] does not exist.\n", atsopt_global) ;
  }
  
  return (S_IXUSR & buf.st_mode) ;
} /* end of file_is_exec */

/* ****** ****** */

// int reference operations

typedef ats_ptr_type ats_intref_type ;

ats_intref_type intref_make (ats_int_type i)
{
  int *r ;
  r = ats_malloc_gc(sizeof(ats_int_type)) ;
  *r = i ; return r ;
}

ats_int_type intref_get (ats_intref_type r)
{
  return *((ats_int_type *)r) ;
}

ats_void_type intref_set (ats_intref_type r, ats_int_type i)
{
  *((ats_int_type *)r) = i ; return ;
}

/* ****** ****** */

ats_int_type
atslib_fork_exec_and_wait_cloptr_exn (ats_ptr_type f_child)
{
  pid_t pid ;
  int status ;

  pid = fork () ;
  if (pid < 0) {
    ats_exit_errmsg (errno, "Exit: [fork] failed.\n") ;
  }
  if (pid > 0) {
    wait (&status) ; ATS_FREE (f_child) ; return status ;
  }
  /* this is the child */
  ((ats_void_type (*)(ats_clo_ptr_type))((ats_clo_ptr_type)f_child)->closure_fun)(f_child) ;
  _exit (0) ; /* no need to flush STDIN, STDOUT and STDERR */
  return 0 ; /* deadcode */
} /* atslib_fork_exec_and_wait_cloptr_exn */

/* ****** ****** */

extern ats_bool_type strlst_is_nil(ats_ptr_type) ;

extern ats_ptr_type strlst_head_get(ats_ptr_type) ;
extern ats_ptr_type strlst_tail_get(ats_ptr_type) ;

ats_void_type
strlst_to_strarr (ats_sum_ptr_type ss, ats_ptr_type p)
{
  while (1) {
    if (strlst_is_nil(ss)) break ;
    *((ats_ptr_type *)p) = strlst_head_get(ss) ;
    p = ((ats_ptr_type *)p) + 1 ; ss = strlst_tail_get(ss) ;
  } /* end of [while] */
  return ;
} /* end of [strlst_to_strarr] */

#define BUFSZ 64

ats_ptr_type
string_trans (ats_ptr_type s0, ats_clo_ptr_type f)
{
  int i, sz;
  char *buf0, *buf1, *p, c, *s ;

  sz = BUFSZ ; buf0 = ats_malloc_gc(sz) ;

  i = 0 ; p = buf0 ;
  while (c = *((char *)s0)) {
    s0 = (char *)s0 + 1 ;
    s = ((ats_ptr_type (*)(ats_clo_ptr_type, ats_char_type))f->closure_fun)(f, c) ;
    while (c = *s) {
      ++s ;
      if (i == sz) {
        buf1 = ats_malloc_gc (sz + sz) ;
        memcpy (buf1, buf0, sz) ;
        ats_free_gc (buf0); buf0 = buf1 ;
        p = buf0 + sz ;
        sz = sz + sz ;
      } /* end of [if] */
      *p = c ; ++i ; ++p ;
    } /* end of [while] */
  } /* end of [while] */

  if (i == sz) {
    buf1 = ats_malloc_gc(sz+1) ;
    memcpy (buf1, buf0, sz) ;
    ats_free_gc (buf0) ; buf0 = buf1 ;
  } /* end of [if] */

  buf0[i] = '\000' ;

  return buf0 ;
} // end of [string_trans]

//

// for the purpose of bootstrapping
ats_ptr_type // already defined in unistd.dats
__ats_getcwd () {
  char *buf, *res ;
  int sz = 64 ;

  buf = ats_malloc_gc(sz) ;

  while (1) {
    res = getcwd (buf, sz) ;
    if (!res) {
      ats_free_gc (buf) ;
      sz = sz + sz ; buf = ats_malloc_gc (sz) ;
      continue ;
    } /* end of [if] */
    break ;
  } /* end of [while] */
  return buf ;
} /* end of [__ats_getcwd] */

%}

(* ****** ****** *)

(* end of [basics.dats] *)
