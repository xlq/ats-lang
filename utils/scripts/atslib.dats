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

// Time: Summer 2007

(* Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

staload "libc/SATS/stdio.sats"
staload "libc/SATS/unistd.sats"

(* ****** ****** *)

staload "top.sats"

(* ****** ****** *)

extern fun gcc_libfile_exec
  (param_rev: Strlst, infile: string, outfile: string): void
  = "gcc_libfile_exec"

implement gcc_libfile_err (param_rev, infile, outfile) = let
  val cmd = lam (): void =<cloptr1> gcc_libfile_exec (param_rev, infile, outfile)
in
  fork_exec_and_wait_cloptr_exn (cmd)
end // end of [gcc_libfile_err]

(* ****** ****** *)

extern fun ar_r_exec (libfile: string, objfile: string): void
  = "ar_r_exec"

// archive with replacement
implement ar_r_err (libfile, objfile) = begin
  fork_exec_and_wait_cloptr_exn (lam () => ar_r_exec (libfile, objfile))
end // end of [ar_r_err]

(* ****** ****** *)

#define i2u uint_of_int

fn char_identifize (c: char):<cloptr1> String =
  if char_isalnum c then tostring c
  else let
    val i = uint_of_char c
    val c1 = i / i2u 16 and c2 = i mod i2u 16
  in
    tostringf_size (4, "_%x%x", @(c1, c2))
  end // end of [if]

implement ccomp_gcc_ar_libfile (param_rev, infile, libfile) = let
  val sfx = suffix_of_filename infile
  val flag_stadyn = (
    if stropt_is_none sfx then begin
      exit_prerrf {int} (
        1, "Exit: [%s]: no filename extension\n.", @(infile)
      )
    end else begin case+ stropt_unsome sfx of
      | "sats" => 0
      | "dats" => 1
      | _ => exit_prerrf {int} (
          1, "Exit: [%s]: unsupported filename extension\n.", @(infile)
        )
    end // end of [if]
  ) : int
  val infull = (
    if filename_is_local infile then
      tostringf_size (64, "%s/%s", @(getcwd (), infile))
    else infile
  ) : string
  val outbase = string_trans (infull, char_identifize)
  val outfile = atslib_output_global + outbase
  val outfile_c = outfile + ".c"
  val status = ccomp_file_to_file_err
    (flag_stadyn, STRLSTnil(*param_ats*), infile, outfile_c)
  val () = 
   if (status <> 0) then exit_prerrf {void}
     (status, "Exit: [ccomp_gcc_ar_libfile(%s)] failed: ccomp\n", @(infile))
   else ()
  val outfile_o = outfile + ".o"
  val status = gcc_libfile_err (param_rev, outfile_c, outfile_o)
  val () =
    if (status <> 0) then begin exit_prerrf {void}
      (status, "Exit: [ccomp_gcc_ar_libfile(%s)] failed: gcc\n", @(infile))
    end
  val status = ar_r_err (libfile, outfile_o)
  val () = if (status <> 0) then begin exit_prerrf {void}
    (status, "Exit: [ccomp_gcc_ar_libfile(%s)] failed: ar\n", @(infile))
  end // end of [val]
in
  printf ("The file [%s] has been compiled and archived.\n", @(infile))
end // end of [ccomp_gcc_ar_libfile]

(* ****** ****** *)

extern fun fget_line {m:fm}
  (pf: file_mode_lte (m, r) | f: &FILE m): String
  = "fget_line"

#define i2sz size1_of_int1

fun library_make_loop {m:fm} {l_file:addr}
  (param_rev: Strlst, file: &FILE r, dir: String, libfilename: string)
  : void = let
  fn filename_is_legal (name: String): bool = let
    val _0 = i2sz 0
  in
    if string_is_at_end (name, _0) then false
    else (if name[_0] = '#' then false else true)
  end // end of [filename_is_legal]
in
  if feof (file) <> 0 then ()
  else let
    val name = fget_line (file_mode_lte_r_r | file)
    val () = if filename_is_legal name then begin
      ccomp_gcc_ar_libfile (param_rev, dir + name, libfilename)
    end // end of [val]
  in
    library_make_loop (param_rev, file, dir, libfilename)
  end (* end of [if] *)
end // end of [library_make_loop]

(* ****** ****** *)

implement libats_make (param_rev) = let
   val libfiles_local = ATSHOME_dir_append ".libfiles_local"
   val (pf_file | p_file) = fopen_exn (libfiles_local, file_mode_r)
in
   library_make_loop (param_rev, !p_file, ATSHOME_dir, libats_global);
   fclose_exn (pf_file | p_file)
end // end of [libats_make]

// implement libats_mt_make () = library_make (libats_mt_global)

(* ****** ****** *)

val libatslex_local = "ccomp/lib/libatslex.a"
val libatslex_global = ATSHOME_dir_append libatslex_local

// this function is currently not in use
implement libatslex_make (param_rev) = let
  val dir = ATSHOME_dir_append "libats/lex/"
in
  ccomp_gcc_ar_libfile (param_rev, dir + "lexing.sats", libatslex_global) ;
  ccomp_gcc_ar_libfile (param_rev, dir + "lexing.dats", libatslex_global) ;
  ccomp_gcc_ar_libfile (param_rev, dir + "tables.dats", libatslex_global) ;
end // end of [libatslex_make]

(* ****** ****** *)

%{^

#include <unistd.h>

#include "libc/CATS/stdio.cats"

typedef ats_ptr_type ats_string_type ;

extern ats_string_type ATSHOME_dir ;
extern ats_string_type runtime_global ;

extern ats_bool_type strlst_is_nil (ats_ptr_type) ;
extern ats_ptr_type strlst_head_get (ats_ptr_type) ;
extern ats_ptr_type strlst_tail_get (ats_ptr_type) ;

ats_void_type
gcc_libfile_exec (
  ats_ptr_type param_rev
, ats_string_type input_c
, ats_string_type output_o
) {
  int err ;
  int n, argc ; char **argv, **argv_p, **argv_p1 ;

  argc = n = strlst_length (param_rev) ;
  argc += 1 ; // self(*first*)
  argc += 2 ; // -I runtime_global
  argc += 2 ; // -I ATSHOME_dir
  argc += 2 ; // -c input_c
  argc += 2 ; // -o output_o
  argc += 1 ; // nullptr(*last)
  argv = (char**)malloc (argc * sizeof(ats_ptr_type)) ;
  if (!argv) {
    fprintf (stderr, "exit(ATS): gcc_libfile_exec: malloc failed!\n") ;
    exit (1) ;
  } // end of [if]
  argv_p = argv ;
  *argv_p = "gcc" ; argv_p += 1 ;
  *argv_p = "-I" ; argv_p += 1 ;
  *argv_p = runtime_global ; argv_p += 1 ;
  *argv_p = "-I" ; argv_p += 1 ;
  *argv_p = ATSHOME_dir ; argv_p += 1 ;
  argv_p += n ; argv_p1 = argv_p ; while (1) {
    if (strlst_is_nil (param_rev)) break ;
    argv_p1 -= 1 ; *argv_p1 = (char*)strlst_head_get (param_rev) ;
    param_rev = strlst_tail_get (param_rev) ;
  }
  *argv_p = "-c" ; argv_p += 1 ; *argv_p = input_c ; argv_p += 1 ;
  *argv_p = "-o" ; argv_p += 1 ; *argv_p = output_o ; argv_p += 1 ;
  *argv_p = (char*)0 ;

// /*
  fputs (*argv, stderr) ; argv_p = argv + 1 ;
  while (*argv_p) {
    fputc (' ', stderr) ; fputs (*argv_p, stderr) ; argv_p += 1 ;
  }
  fputc ('\n', stderr) ;
// */

  err = execvp("gcc", argv) ;
  if (err < 0) perror ("ccomp_file_to_file_exec: [execvp] failed: ") ;
  exit (1) ;

  return ;
}

ats_void_type
ar_r_exec (ats_string_type lib, ats_string_type output_o) {
  execlp("ar", "ar", "-r", lib, output_o, (char*)0) ;
  return ;
}

#define INCSZ 1024

ats_string_type fget_line (ats_ptr_type file) {
  int c;
  int i, sz;
  char *buf0, *buf1, *p;

  if (feof((FILE *)file)) {
    ats_exit_errmsg(1, (ats_string_type)"Exit: [fget_line] failed: EOF\n");
  }

  sz = INCSZ;
  buf0 = (char*)ats_malloc_gc(sz); p = buf0;

  while (1) {
    for (i = 0; i < INCSZ; ++i) {
      c = fgetc ((FILE *)file) ;
      if (c == '\n' || c == EOF) { *p = '\000'; return buf0; }
      *p = c; ++p;
    }
    buf1 = (char*)ats_malloc_gc (sz + INCSZ) ;
    memcpy (buf1, buf0, sz) ;
    ats_free_gc (buf0) ;    
    buf0 = buf1 ; p = buf0 + sz;
    sz = sz + INCSZ ;
  }

  return (char*)0 ; /* deadcode */
} /* end of [fget_line] */

%}

(* ****** ****** *)

(* end of [atslib.dats] *)
