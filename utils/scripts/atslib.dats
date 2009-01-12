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

extern fun gcc_libfile_exec (infile: string, outfile: string): void
  = "gcc_libfile_exec"

implement gcc_libfile_err (infile, outfile) = let
  val cmd = lam (): void =<cloptr1> gcc_libfile_exec (infile, outfile)
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

implement ccomp_gcc_ar_libfile (infile, libfile) = let
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
    (flag_stadyn, STRLSTnil(*param*), infile, outfile_c)
  val () = 
   if (status <> 0) then exit_prerrf {void}
     (status, "Exit: [ccomp_gcc_ar_libfile(%s)] failed: ccomp\n", @(infile))
   else ()
  val outfile_o = outfile + ".o"
  val status = gcc_libfile_err (outfile_c, outfile_o)
  val () =
    if (status <> 0) then begin exit_prerrf {void}
      (status, "Exit: [ccomp_gcc_ar_libfile(%s)] failed: gcc\n", @(infile))
    end
  val status = ar_r_err (libfile, outfile_o)
  val () =
    if (status <> 0) then begin exit_prerrf {void}
      (status, "Exit: [ccomp_gcc_ar_libfile(%s)] failed: ar\n", @(infile))
    end
in
  printf ("The file [%s] has been compiled and archived.\n", @(infile))
end // end of [ccomp_gcc_ar_libfile]

(* ****** ****** *)

extern fun fget_line {m:fm}
  (pf: file_mode_lte (m, r) | f: &FILE m): String
  = "fget_line"

fun library_make_loop {m:fm} {l_file:addr}
  (file: &FILE r, dir: String, libfilename: string)
  : void = let
  fn filename_is_legal (name: String): bool =
    if string_is_at_end (name, 0) then false
    else (if name[0] = '#' then false else true)
in
  if feof (file) <> 0 then ()
  else let
    val name = fget_line (file_mode_lte_r_r | file)
    val () =
      if filename_is_legal name then begin
        ccomp_gcc_ar_libfile (dir + name, libfilename)
      end
  in
    library_make_loop (file, dir, libfilename)
  end
end // end of [library_make_loop]

(* ****** ****** *)

implement libats_make () = let
   val libfiles_local = ATSHOME_dir_append ".libfiles_local"
   val (pf_file | p_file) = fopen_exn (libfiles_local, file_mode_r)
in
   library_make_loop (!p_file, ATSHOME_dir, libats_global);
   fclose_exn (pf_file | p_file)
end // end of [libats_make]

// implement libats_mt_make () = library_make (libats_mt_global)

(* ****** ****** *)

val libatslex_local = "ccomp/lib/libatslex.a"
val libatslex_global = ATSHOME_dir_append libatslex_local

// this function is currently not in use
implement libatslex_make () = let
  val dir = ATSHOME_dir_append "libats/lex/"
in
  ccomp_gcc_ar_libfile (dir + "lexing.sats", libatslex_global) ;
  ccomp_gcc_ar_libfile (dir + "lexing.dats", libatslex_global) ;
  ccomp_gcc_ar_libfile (dir + "tables.dats", libatslex_global) ;
end // end of [libatslex_make]

(* ****** ****** *)

%{^

#include <unistd.h>

#include "libc/CATS/stdio.cats"

typedef ats_ptr_type ats_string_type ;

extern ats_string_type ATSHOME_dir ;
extern ats_string_type runtime_global ;

ats_void_type
gcc_libfile_exec
  (ats_string_type input_c, ats_string_type output_o) {
  execlp(
    "gcc", "gcc",
    "-I", runtime_global, "-I", ATSHOME_dir, "-O3",
    "-o", output_o, "-c", input_c, (char *)0
  ) ;
  return ;
}

ats_void_type
ar_r_exec (ats_string_type lib, ats_string_type output_o) {
  execlp("ar", "ar", "-r", lib, output_o, (char *)0) ;
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
  buf0 = (char *)ats_malloc_gc(sz); p = buf0;

  while (1) {
    for (i = 0; i < INCSZ; ++i) {
      c = fgetc ((FILE *)file) ;
      if (c == '\n' || c == EOF) { *p = '\000'; return buf0; }
      *p = c; ++p;
    }
    buf1 = (char *)ats_malloc_gc (sz + INCSZ) ;
    memcpy (buf1, buf0, sz) ;
    ats_free_gc (buf0) ;    
    buf0 = buf1 ; p = buf0 + sz;
    sz = sz + INCSZ ;
  }

  return (char *)0 ; /* deadcode */
}

%}

(* ****** ****** *)

(* end of [atslib.dats] *)
