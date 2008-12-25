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

// Time: Summer 2008

(* Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

//
// The command [atspack] is called to make an ATS package for release
//

//
// This is done in ATS (instead of in a scripting language like PERL) largely
// because I want to test some functions declared in [libc/SATS/stdio.sats].
// Also, this exercise should help myself become a bit more familiar with the
// Linux file system in general.
//

(* ****** ****** *)

staload "prelude/SATS/file.sats"

(* ****** ****** *)

staload "libc/SATS/stdio.sats"
staload "libc/SATS/stdlib.sats"

staload "libc/SATS/dirent.sats"

staload "libc/sys/SATS/stat.sats"

staload "libc/sys/SATS/types.sats"

(* ****** ****** *)

#define ATSPACKAGE_NAME "ats-lang-anairiats"

(* ****** ****** *)

extern fun dirent_name_get (dir: &DIR): Stropt = "dirent_name_get"

%{^

extern ats_ptr_type
atspre_string_make_substring (
  const ats_ptr_type src0, const ats_int_type start, const ats_int_type len
) ; /* atspre_string_make_substring */

static inline
ats_ptr_type dirent_name_get(ats_ptr_type dir) {
  struct dirent *ent ;
  ent = readdir((DIR*)dir) ;
  if (ent) { return
    atspre_string_make_substring (ent->d_name, 0, strlen(ent->d_name)) ;
  } else {
    return (char*)0 ;
  }
}  /* end of [dirent_name_get] */ 

%}

(* ****** ****** *)

fn getenv_exn (name: string): String = let
  val stropt = getenv_opt name
in
  if stropt_is_some stropt then
    string1_of_string0 (stropt_unsome stropt)
  else begin
    prerr "The environment variable [";
    prerr name;
    prerr "] is undefined!\n" ;
    exit (1)
  end
end // end of [getenv_exn]

val ATSHOME = let
  val str = getenv_exn ("ATSHOME")
(*
  val lst = string_length (str) - 1
  val () = if str[lst] = dirsep then str[lst] = '\000' else ()
*)
in
  str // return value
end

val SRCROOT = ATSHOME + "/"

(* ****** ****** *)

fn ATSPACKAGE_VERSION_get (): string = let
  val name = SRCROOT + "VERSION.txt"
  val () = begin
    if ~(test_file_exists name) then begin
      prerr "The file ["; prerr name; prerr "] is not available.";
      prerr_newline ();
      exit (1)
    end // end of [if]
  end
  val fil = open_file (name, file_mode_r)
  val version = input_line (fil)
  val () = close_file (fil)
(*
  val () = begin
    prerr "ATSPACKAGE_VERSION_get: version = "; prerr version;
    prerr_newline ()
  end
*)
in
  version
end // end of [ATSPACKAGE_VERSION_get]

val ATSPACKAGE_VERSION: string = ATSPACKAGE_VERSION_get ()

val DSTROOT: string = begin
  string_concat '[ATSPACKAGE_NAME, "-", ATSPACKAGE_VERSION, "/"]
end // end of [DSTROOT]

(* ****** ****** *)

#define BUFSZ 8192

// there are certainly faster ways to copy files, but this code offers
// an opportunity to test ATS :)
fn fcopy_exn (src: string, dst: string): void = let
(*
  val () = begin
    prerr "fopen_exn: src = "; prerr src; prerr_newline ();
    prerr "fopen_exn: dst = "; prerr dst; prerr_newline ();
  end
*)
  val (pf_src | p_src) = fopen_exn (src, file_mode_r)
  val (pf_dst | p_dst) = fopen_exn (dst, file_mode_w)
(*
  val [l_buf:addr] (pf_gc, pf_buf | p_buf) = malloc_gc (BUFSZ)
*)
  var !p_buf with pf_buf = @[byte][BUFSZ]()
  prval () = pf_buf := bytes_v_of_b0ytes_v (pf_buf)
  fun loop (
      pf_buf: !bytes (BUFSZ) @ p_buf | p_buf: ptr p_buf, src: &FILE r, dst: &FILE w
    ) : void =
    if feof (src) <> 0 then () else let
      val nread = fread_byte (file_mode_lte_r_r | !p_buf, BUFSZ, src)
      val () = fwrite_byte_exn (file_mode_lte_w_w | !p_buf, nread, dst)
    in
      loop (pf_buf | p_buf, src, dst)
    end // end of [loop]
  val () = loop (pf_buf | p_buf, !p_src, !p_dst)
(*
  val () = free_gc (pf_gc, pf_buf | p_buf)
*)
in
  fclose_exn (pf_src | p_src); fclose_exn (pf_dst | p_dst)
end // end of [fcopy_exn]

(* ****** ****** *)

val DIRmode: mode_t = begin
  S_IRWXU // lor S_IRGRP lor S_IXGRP lor S_IROTH lor S_IXOTH)
end // end of [DIRmode]

(* ****** ****** *)

fn dir_copy
  (srcdir: string, dstdir: string, test: string -> bool) = let
  val srcdir = string1_of_string0 srcdir
  and dstdir = string1_of_string0 dstdir

  macdef cp (name) = fcopy_exn (srcdir + ,(name), dstdir + ,(name))

  fun loop (dir: &DIR):<cloref1> void = let
    val name = dirent_name_get (dir)
  in
    case+ 0 of
    | _ when stropt_is_some name => let
        val name = stropt_unsome (name)
        val () = case+ name of
          | _ when test (name) => cp (name) | _ => ()
      in
        loop (dir)
      end // end of [_ when ...]
    | _ => ()
  end // end of [loop]
  val (pf_dir | p_dir) = opendir_exn (srcdir)
  val () = loop (!p_dir)
  val () = closedir_exn (pf_dir | p_dir)
in
  // empty
end // end of [dir_copy]


(* ****** ****** *)

val SRCROOTccomp = SRCROOT + "ccomp/"
val DSTROOTccomp = DSTROOT + "ccomp/"

val SRCROOTccomp_lib = SRCROOTccomp + "lib/"
val DSTROOTccomp_lib = DSTROOTccomp + "lib/"

val SRCROOTccomp_lib_output = SRCROOTccomp_lib + "output/"
val DSTROOTccomp_lib_output = DSTROOTccomp_lib + "output/"

val SRCROOTccomp_runtime = SRCROOTccomp + "runtime/"
val DSTROOTccomp_runtime = DSTROOTccomp + "runtime/"

val SRCROOTccomp_runtime_GCATS = SRCROOTccomp_runtime + "GCATS/"
val DSTROOTccomp_runtime_GCATS = DSTROOTccomp_runtime + "GCATS/"

(*
val SRCROOTsrc = SRCROOT + "src/"; val DSTROOTsrc = DSTROOT + "src/"
*)

(* ****** ****** *)

datatype packnd =
  | PACKNDsource | PACKNDprecompiled

fn packnd_is_source (knd: packnd): bool = begin
  case+ knd of
  | PACKNDsource () => true | PACKNDprecompiled () => false
end // end of [packnd_is_precompile]

fn packnd_is_precompiled (knd: packnd): bool = begin
  case+ knd of
  | PACKNDsource () => false | PACKNDprecompiled () => true
end // end of [packnd_is_precompile]

(* ****** ****** *)

fn bin_dir_copy (knd: packnd): void = let
  val SRCROOTbin = SRCROOT + "bin/"
  val DSTROOTbin = DSTROOT + "bin/"

  macdef cp (name) = fcopy_exn
     (SRCROOTbin + ,(name), DSTROOTbin + ,(name))
  macdef cpx (name) = let
    val src_name = SRCROOTbin + ,(name)
    val dst_name = DSTROOTbin + ,(name)
    val () = fcopy_exn (src_name, dst_name)
    val () = chmod_exn (dst_name, S_IRWXU)
  in
    // empty
  end // end of [cpx]

  val () = mkdir_exn (DSTROOTbin, DIRmode)
  // for keeping the directory from being removed
  val () = cp (".keeper")
  val () = begin
    if (packnd_is_precompiled knd) then (cpx "atscc"; cpx "atsopt")
  end // end of [begin]
in
  prerr "The [bin] directory is successfully copied.";
  prerr_newline ()
end // end of [bin]

(* ****** ****** *)

fun name_is_c (name: string): bool = let
  val name = string1_of_string0 name
  val n = string1_length (name)
in
  if (n >= 2) then
    if (name[n-2] <> '.') then false
    else if name[n-1] <> 'c' then false
    else true
  else false
end // end of [name_is_c]

fun name_is_cats (name: string): bool = let
  val name = string1_of_string0 name
  val n = string1_length (name)
in
  if (n >= 5) then
    if (name[n-5] <> '.') then false
    else if name[n-4] <> 'c' then false
    else if name[n-3] <> 'a' then false
    else if name[n-2] <> 't' then false
    else if name[n-1] <> 's' then false
    else true
  else false
end // end of [name_is_cats]

fun name_is_dats (name: string): bool = let
  val name = string1_of_string0 name
  val n = string1_length (name)
in
  if (n >= 5) then
    if (name[n-5] <> '.') then false
    else if name[n-4] <> 'd' then false
    else if name[n-3] <> 'a' then false
    else if name[n-2] <> 't' then false
    else if name[n-1] <> 's' then false
    else true
  else false
end // end of [name_is_dats]

fun name_is_sats (name: string): bool = let
  val name = string1_of_string0 name
  val n = string1_length (name)
in
  if (n >= 5) then
    if (name[n-5] <> '.') then false
    else if name[n-4] <> 's' then false
    else if name[n-3] <> 'a' then false
    else if name[n-2] <> 't' then false
    else if name[n-1] <> 's' then false
    else true
  else false
end // end of [name_is_sats]

fun name_is_xats (name: string): bool = let
  val name = string1_of_string0 name
  val n = string1_length (name)
in
  if (n >= 5) then
    if (name[n-5] <> '.') then false
    else if name[n-3] <> 'a' then false
    else if name[n-2] <> 't' then false
    else if name[n-1] <> 's' then false
    else true
  else false
end // end of [name_is_cats]

(* ****** ****** *)

fn bootstrap_dir_copy () = let
  val SRCROOTbootstrap = SRCROOT + "bootstrap1/"
  val DSTROOTbootstrap = DSTROOT + "bootstrap1/"

  fn test
    (name: string): bool = begin
    case+ name of
    | _ when name_is_c (name) => true
    | _ when name_is_cats (name) => true
    | _ => false
  end // end of [test]

  macdef cp (name) = fcopy_exn
     (SRCROOTbootstrap + ,(name), DSTROOTbootstrap + ,(name))

  val () = mkdir_exn (DSTROOTbootstrap, DIRmode)
  val () = dir_copy (SRCROOTbootstrap, DSTROOTbootstrap, test)
  val () = cp "ats_grammar_yats.h"
in
  prerr "The [bootstrap] directory is successfully copied.";
  prerr_newline ()
end // end of [bootscrap_dir_copy]

(* ****** ****** *)

fn ccomp_lib_dir_copy (knd: packnd): void = let
  val () = mkdir_exn (DSTROOTccomp_lib, DIRmode)
  val () = begin
    if (packnd_is_precompiled knd) then fcopy_exn
      (SRCROOTccomp_lib + "libats.a", DSTROOTccomp_lib + "libats.a")
  end // end of [val]
  val () = mkdir_exn (DSTROOTccomp_lib_output, DIRmode)
  val () = fcopy_exn // keeping the directory from being removed
     (SRCROOTccomp_lib_output + ".keeper", DSTROOTccomp_lib_output + ".keeper")
in
  // empty
end // end of [ccomp_lib_dir_copy]

(* ****** ****** *)

fn ccomp_runtime_GCATS_dir_copy (knd: packnd): void = let
  fn test (name: string): bool = begin case+ name of
    | _ when name_is_xats (name) => true | _ => false
  end // end of [filename_test]

  macdef cp (name) = fcopy_exn (
    SRCROOTccomp_runtime_GCATS + ,(name), DSTROOTccomp_runtime_GCATS + ,(name)
  ) // end of [fcopy_exn]

  val () = mkdir_exn (DSTROOTccomp_runtime_GCATS, DIRmode)
  val () = dir_copy (
    SRCROOTccomp_runtime_GCATS, DSTROOTccomp_runtime_GCATS, test
  ) // end of [dir_copy]
  val () = begin
    cp "Makefile"; cp "README"; cp "gc.h"
  end
  val () = begin
    if (packnd_is_precompiled knd) then (cp "gc.o"; cp "gc_mt.o")
  end // end of [val]
in
  prerr "The [ccomp/runtime/GCATS] directory is successfully copied.";
  prerr_newline ()
end // end of [ccomp_runtime_GCATS_dir_copy]

//

fn ccomp_runtime_dir_copy (knd: packnd): void = let
  macdef cp (name) = fcopy_exn (
    SRCROOTccomp_runtime + ,(name), DSTROOTccomp_runtime + ,(name)
  )
  val () = mkdir_exn (DSTROOTccomp_runtime, DIRmode)
in
  cp "ats_basics.h";
  cp "ats_exception.h";
  cp "ats_memory.h";
  cp "ats_types.h";
  cp "ats_prelude.c";
  ccomp_runtime_GCATS_dir_copy (knd);
  prerr "The [ccomp/runtime] directory is successfully copied.";
  prerr_newline ()
end // end of [ccomp_runtime_dir_copy]

//

fn ccomp_dir_copy (knd: packnd): void = let
  val () = mkdir_exn (DSTROOTccomp, DIRmode)
  val () = ccomp_lib_dir_copy (knd)
  val () = ccomp_runtime_dir_copy (knd)
in
  // empty
end // end of [ccomp_dir_copy]

(* ****** ****** *)

fn doc_dir_copy () = let
  val SRCROOTdoc = SRCROOT + "doc/"
  val DSTROOTdoc = DSTROOT + "doc/"
  val () = mkdir_exn (DSTROOTdoc, DIRmode)
  val () = fcopy_exn (
    SRCROOTdoc + "FAQ.txt", DSTROOTdoc + "FAQ.txt"
  ) // end of [fcopy_exn]
(*
//
  val SRCROOTdoc_BOOK = SRCROOTdoc + "BOOK/"
  val DSTROOTdoc_BOOK = DSTROOTdoc + "BOOK/"
  val () = mkdir_exn (DSTROOTdoc_BOOK, DIRmode)
  val SRCROOTdoc_BOOK_manual = SRCROOTdoc_BOOK + "manual/"
  val DSTROOTdoc_BOOK_manual = DSTROOTdoc_BOOK + "manual/"
  val () = mkdir_exn (DSTROOTdoc_BOOK_manual, DIRmode)
  val () = fcopy_exn (
    SRCROOTdoc_BOOK_manual + "manual_main.ps"
  , DSTROOTdoc_BOOK_manual + "manual_main.ps"
  ) // end of [fcopy_exn]
  val () = fcopy_exn (
    SRCROOTdoc_BOOK_manual + "manual_main.pdf"
  , DSTROOTdoc_BOOK_manual + "manual_main.pdf"
  ) // end of [fcopy_exn]
//
*)
  val SRCROOTdoc_EXAMPLE = SRCROOTdoc + "EXAMPLE/"
  val DSTROOTdoc_EXAMPLE = DSTROOTdoc + "EXAMPLE/"
  val () = mkdir_exn (DSTROOTdoc_EXAMPLE, DIRmode)
//  
  val SRCROOTdoc_EXAMPLE_INTRO = SRCROOTdoc_EXAMPLE + "INTRO/"
  val DSTROOTdoc_EXAMPLE_INTRO = DSTROOTdoc_EXAMPLE + "INTRO/"
  val () = mkdir_exn (DSTROOTdoc_EXAMPLE_INTRO, DIRmode)
  macdef cp (name) = fcopy_exn (
    SRCROOTdoc_EXAMPLE_INTRO + ,(name), DSTROOTdoc_EXAMPLE_INTRO + ,(name)
  )
  val () = cp "Makefile"
  val () = cp "HelloWorld.dats"
  val () = cp "f91.dats"
  val () = cp "fact1.dats"
  val () = cp "fact2.dats"
  val () = cp "fact3.dats"
  val () = cp "fibs.dats"
//
  val SRCROOTdoc_EXAMPLE_MISC = SRCROOTdoc_EXAMPLE + "MISC/"
  val DSTROOTdoc_EXAMPLE_MISC = DSTROOTdoc_EXAMPLE + "MISC/"
  val () = mkdir_exn (DSTROOTdoc_EXAMPLE_MISC, DIRmode)
  macdef cp (name) = fcopy_exn (
    SRCROOTdoc_EXAMPLE_MISC + ,(name), DSTROOTdoc_EXAMPLE_MISC + ,(name)
  )
  val () = cp "Makefile"
  val () = cp "AutoDiff.dats"
  val () = cp "fft.dats"
  val () = cp "GarsiaWachs.dats"
  val () = cp "GaussElim.dats"
  val () = cp "hamming_lazy.dats"
  val () = cp "hanoi.dats"
  val () = cp "kmp.dats"
  val () = cp "pi_lazy.dats"
  val () = cp "passwdgen.dats"
  val () = cp "queens.dats"
  val () = cp "sieve.dats"
  val () = cp "sieve_lazy.dats"
  val () = cp "strmat.dats"
  val () = cp "sumup.dats"
  val () = cp "tetrix.dats"
  val () = cp "wc.dats"
//
  val SRCROOTdoc_EXAMPLE_MISC = SRCROOTdoc_EXAMPLE + "MISC/Twentyfour/"
  val DSTROOTdoc_EXAMPLE_MISC = DSTROOTdoc_EXAMPLE + "MISC/Twentyfour/"
  val () = mkdir_exn (DSTROOTdoc_EXAMPLE_MISC, DIRmode)
  macdef cp (name) = fcopy_exn (
    SRCROOTdoc_EXAMPLE_MISC + ,(name), DSTROOTdoc_EXAMPLE_MISC + ,(name)
  )
  val () = cp "Makefile"
  val () = cp "rational.sats"
  val () = cp "rational.dats"
  val () = cp "twentyfour.dats"
//
  val SRCROOTdoc_EXAMPLE_MISC = SRCROOTdoc_EXAMPLE + "MISC/HttpServer/"
  val DSTROOTdoc_EXAMPLE_MISC = DSTROOTdoc_EXAMPLE + "MISC/HttpServer/"
  val () = mkdir_exn (DSTROOTdoc_EXAMPLE_MISC, DIRmode)
  macdef cp (name) = fcopy_exn (
    SRCROOTdoc_EXAMPLE_MISC + ,(name), DSTROOTdoc_EXAMPLE_MISC + ,(name)
  )
  val () = cp "Makefile"
  val () = cp "server.dats"
//
  val SRCROOTdoc_EXAMPLE_OpenGL = SRCROOTdoc_EXAMPLE + "OpenGL/"
  val DSTROOTdoc_EXAMPLE_OpenGL = DSTROOTdoc_EXAMPLE + "OpenGL/"
  val () = mkdir_exn (DSTROOTdoc_EXAMPLE_OpenGL, DIRmode)
  macdef cp (name) = fcopy_exn (
    SRCROOTdoc_EXAMPLE_OpenGL + ,(name), DSTROOTdoc_EXAMPLE_OpenGL + ,(name)
  )
  val () = cp "Makefile"
  val () = dir_copy
    (SRCROOTdoc_EXAMPLE_OpenGL, DSTROOTdoc_EXAMPLE_OpenGL, name_is_xats)
in
  prerr "The [doc] directory is successfully copied.";
  prerr_newline ()
end // end of [doc_dir_copy]

(* ****** ****** *)

fn lib_dir_copy
  (srclibname: string, dstlibname: string): void = let
  val srclibname = string1_of_string0 srclibname
  and dstlibname = string1_of_string0 dstlibname
  val () = mkdir_exn (dstlibname, DIRmode)

  val srclibname_CATS = srclibname + "CATS/"
  val dstlibname_CATS = dstlibname + "CATS/"
  val () = mkdir_exn (dstlibname_CATS, DIRmode)
  val () = dir_copy
    (srclibname_CATS, dstlibname_CATS, name_is_cats)

  val srclibname_DATS = srclibname + "DATS/"
  val dstlibname_DATS = dstlibname + "DATS/"
  val () = mkdir_exn (dstlibname_DATS, DIRmode)
  val () = dir_copy
    (srclibname_DATS, dstlibname_DATS, name_is_dats)

  val srclibname_SATS = srclibname + "SATS/"
  val dstlibname_SATS = dstlibname + "SATS/"
  val () = mkdir_exn (dstlibname_SATS, DIRmode)
  val () = dir_copy
    (srclibname_SATS, dstlibname_SATS, name_is_sats)
in
  // empty
end // end of [lib_dir_copy]

(* ****** ****** *)

fn prelude_dir_copy () = let
  val SRCROOTprelude = SRCROOT + "prelude/"
  val DSTROOTprelude = DSTROOT + "prelude/"
  macdef cp (name) = fcopy_exn (
    SRCROOTprelude + ,(name), DSTROOTprelude + ,(name)
  )
  val () = lib_dir_copy (SRCROOTprelude, DSTROOTprelude)
  val () = cp "fixity.ats"
  val () = cp "basics_sta.sats"
  val () = cp "basics_dyn.sats"
  val () = cp "macrodef.sats"
  val () = cp "params.hats"
  val () = cp "params_system.hats"
  val () = cp "sortdef.sats"
  val () = cp "ats_main_prelude.dats"
in
  prerr "The [prelude] directory is successfully copied.";
  prerr_newline ()
end // end of [prelude_dir_copy]

fn libc_dir_copy () = let
  val SRCROOTlibc = SRCROOT + "libc/"
  val DSTROOTlibc = DSTROOT + "libc/"
  val () = lib_dir_copy (SRCROOTlibc, DSTROOTlibc)
  val SRCROOTlibc_sys = SRCROOTlibc + "sys/"
  val DSTROOTlibc_sys = DSTROOTlibc + "sys/"
  val () = lib_dir_copy (SRCROOTlibc_sys, DSTROOTlibc_sys)
  val SRCROOTlibc_GL = SRCROOTlibc + "GL/"
  val DSTROOTlibc_GL = DSTROOTlibc + "GL/"
  val () = lib_dir_copy (SRCROOTlibc_GL, DSTROOTlibc_GL)
in
  prerr "The [libc] directory is successfully copied.";
  prerr_newline ()
end // end of [libc_dir_copy]

fn libats_dir_copy () = let
  val SRCROOTlibats = SRCROOT + "libats/"
  val DSTROOTlibats = DSTROOT + "libats/"
  val () = lib_dir_copy (SRCROOTlibats, DSTROOTlibats)
  // the code for ATS lexer is in [libats/lex]
  val SRCROOTlibatslex = SRCROOTlibats + "lex/"
  val DSTROOTlibatslex = DSTROOTlibats + "lex/"
  val () = mkdir_exn (DSTROOTlibatslex, DIRmode)
  val () = dir_copy (SRCROOTlibatslex, DSTROOTlibatslex, name_is_xats)
in
  prerr "The [libats] directory is successfully copied.";
  prerr_newline ()
end // end of [libats_dir_copy]

(* ****** ****** *)

(*
fn src_dir_copy (): void = let
  fn test (name: string): bool = begin case+ name of
    | _ when name_is_xats (name) => true | _ => false
  end // end of [filename_test]

  macdef cp (name) =
    fcopy_exn (SRCROOTsrc + ,(name), DSTROOTsrc + ,(name))

  val () = mkdir_exn (DSTROOTsrc, DIRmode)
  val () = dir_copy (SRCROOTsrc, DSTROOTsrc, test)
  val () = cp "Makefile"
  val () = cp "Makefile_bootstrap"
  val () = cp "ats_grammar_yats.c"
  val () = cp "ats_grammar_yats.h"
in
  prerr "The [src] directory is successfully copied.";
  prerr_newline ()
end // end of [src_dir_copy]
*)

(* ****** ****** *)

fn utils_dir_copy () = let
  val SRCROOTutils = SRCROOT + "utils/"
  val DSTROOTutils = DSTROOT + "utils/"
  val () = mkdir_exn (DSTROOTutils, DIRmode)
//
  val SRCROOTutils_atslex = SRCROOTutils + "atslex/"
  val DSTROOTutils_atslex = DSTROOTutils + "atslex/"
  val () = mkdir_exn (DSTROOTutils_atslex, DIRmode)
  val () = dir_copy
    (SRCROOTutils_atslex, DSTROOTutils_atslex, name_is_xats)
  val () = fcopy_exn (
    SRCROOTutils_atslex + "Makefile", DSTROOTutils_atslex + "Makefile"
  ) // end of [fcopy_exn]
  val () = fcopy_exn (
    SRCROOTutils_atslex + "README", DSTROOTutils_atslex + "README"
  ) // end of [fcopy_exn]
//
  val SRCROOTutils_atslex_EXAMPLE = SRCROOTutils_atslex + "EXAMPLE/"
  val DSTROOTutils_atslex_EXAMPLE = DSTROOTutils_atslex + "EXAMPLE/"
  val () = mkdir_exn (DSTROOTutils_atslex_EXAMPLE, DIRmode)
  val () = dir_copy
    (SRCROOTutils_atslex_EXAMPLE, DSTROOTutils_atslex_EXAMPLE, name_is_xats)
  val () = fcopy_exn (
    SRCROOTutils_atslex_EXAMPLE + "Makefile"
  , DSTROOTutils_atslex_EXAMPLE + "Makefile"
  ) // end of [fcopy_exn]
//
  val SRCROOTutils_scripts = SRCROOTutils + "scripts/"
  val DSTROOTutils_scripts = DSTROOTutils + "scripts/"
  val () = mkdir_exn (DSTROOTutils_scripts, DIRmode)
  val () = dir_copy
    (SRCROOTutils_scripts, DSTROOTutils_scripts, name_is_xats)
  val () = fcopy_exn (
    SRCROOTutils_scripts + "Makefile", DSTROOTutils_scripts + "Makefile"
  ) // end of [fcopy_exn]
in
  prerr "The [utils] directory is successfully copied.";
  prerr_newline ()
end // end of [utils_dir_copy]

(* ****** ****** *)

extern fun atspack_source_code (): void

implement atspack_source_code () = let
  val () = // run-time checking
    if test_file_exists (DSTROOT) then begin
      prerr "The directory ["; prerr DSTROOT; prerr "] already exists.";
      prerr_newline ();
      exit (1)
    end // end of [if]
  val () = mkdir_exn (DSTROOT, DIRmode)

  macdef cp name =
    fcopy_exn (SRCROOT + ,(name), DSTROOT + ,(name))
  macdef cp2 name1 name2 =
    fcopy_exn (SRCROOT + ,(name1), DSTROOT + ,(name2))
  macdef cpx (name) = let
    val src_name = SRCROOT + ,(name)
    val dst_name = DSTROOT + ,(name)
    val () = fcopy_exn (src_name, dst_name)
    val () = chmod_exn (dst_name, S_IRWXU)
  in
    // empty
  end // end of [cpx]
  val () = cp "INSTALL"
  val () = cp "VERSION.txt"
  val () = cp2 "Makefile_distribute" "Makefile"
  val () = cp "atshomecheck.sh"
  val () = cpx "configure"
  val () = cp "configure.ac"
  val () = cp "config.h.in"
  val () = cp ".libfiles"
  val () = cp ".bootstrap_header"
  val () = cp ".bootstrap_makefile"

  val () = bin_dir_copy (PACKNDsource)
  val () = bootstrap_dir_copy ()
  val () = ccomp_dir_copy (PACKNDsource)
  val () = doc_dir_copy ()
  val () = prelude_dir_copy ()
  val () = libc_dir_copy ()
  val () = libats_dir_copy ()
(*
  val () = src_dir_copy () // The source code is no longer distributed
*)
  val () = utils_dir_copy ()

in
  prerr "The package [";
  prerr ATSPACKAGE_NAME;
  prerr "-";
  prerr ATSPACKAGE_VERSION;
  prerr "] is successfully built.";
  prerr_newline ()  
end // end of [atspack_source_code]

(* ****** ****** *)

extern fun atspack_precompiled (): void

implement atspack_precompiled () = let
  val () = // run-time checking
    if test_file_exists (DSTROOT) then begin
      prerr "The directory ["; prerr DSTROOT; prerr "] already exists.";
      prerr_newline ();
      exit (1)
    end // end of [if]
  val () = mkdir_exn (DSTROOT, DIRmode)

  macdef cp (name) = fcopy_exn (SRCROOT + ,(name), DSTROOT + ,(name))
  val () = cp "INSTALL"
  val () = cp "config.h"
  val () = bin_dir_copy (PACKNDprecompiled)
  val () = ccomp_dir_copy (PACKNDprecompiled)
  val () = prelude_dir_copy ()
  val () = libc_dir_copy ()
  val () = libats_dir_copy ()
in
  // empty
end // end of [atspack_precompiled]

(* ****** ****** *)

implement main (argc, argv) = let
  var knd: packnd = PACKNDsource; val () = begin case+ argc of
  | _ when argc >= 2 => let
      val argv1 = argv.[1] in case+ argv1 of
      | _ when (argv1 = "--precompiled") => knd := PACKNDprecompiled ()
      | _ when (argv1 = "--source") => ()
      | _ => let
          val cmd = argv.[0]
        in
          prerr "["; prerr argv.[0]; prerr "]";
          prerr ": Unrecognized flag: "; prerr argv1;
          prerr_newline ();
          exit {void} (1)
        end // end of [_]
    end // end of [argc >= 2]
  | _ => ()
  end // end of [val]
in
  case+ 0 of
  | _ when (packnd_is_source knd) => atspack_source_code ()
  | _ when (packnd_is_precompiled knd) => atspack_precompiled ()
  | _ => ()
end // end of [main]

(* ****** ****** *)

(* end of [atspack.dats] *)
