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

%{^

#include "libc/CATS/stdio.cats"
#include "libc/CATS/stdlib.cats"
#include "libc/sys/CATS/types.cats" // for [pid_t]
#include "libc/CATS/unistd.cats"

typedef ats_ptr_type ats_intref_type ;

%}

(* ****** ****** *)

staload "top.sats"

(* ****** ****** *)

fn do_usage (cmd: string): void = begin
  printf ("The usage of %s is:\n", @(cmd));
  printf ("  %s [flag-or-file]*\n", @(cmd));
end // end of [do_usage]

(* ****** ****** *)

#define nil STRLSTnil; #define :: STRLSTcons

fn string_is_flag (s: string):<fun0> bool = let
  val s = string1_of_string s
in
  if string_is_empty s then false else begin
    string_get_char_at (s, size1_of_int1 0) = '-'
  end // end of [if]
end // end of [string_is_flag]

(* ****** ****** *)

extern fun IATS_wait_set (): void = "IATS_wait_set"
extern fun IATS_wait_is_set (): bool = "IATS_wait_is_set"
extern fun IATS_wait_clear (): void = "IATS_wait_clear"

extern fun IATS_extract (s: string): Stropt = "IATS_extract"

extern fun flag_is_IATSdir (s: string): bool = "flag_is_IATSdir"

(* ****** ****** *)

fn flag_is_compile_only (flag: string):<fun0> Bool =
  case+ flag of "-cc" => true | "--compile" => true | _ => false

val is_compile_only: intref = intref_make 0
extern val "is_compile_only" = is_compile_only

//

fn flag_is_typecheck_only (flag: string):<fun0> Bool = begin
  case+ flag of "-tc" => true | "--typecheck" => true | _ => false
end // end of [flag_is_typecheck_only]

val is_typecheck_only: intref = intref_make 0
extern val "is_typecheck_only" = is_typecheck_only

//

fn flag_is_objcode_only (flag: string):<fun0> Bool =
  case+ flag of "-c" => true | _ => false

val is_objcode_only: intref = intref_make 0
extern val "is_objcode_only" = is_objcode_only

//

fn flag_is_version (flag: string):<fun0> Bool =
  case+ flag of "-v" => true | "--version" => true | _ => false

(* ****** ****** *)

fn flag_is_ATS_GC (flag: string): Bool = begin
  case+ flag of "-D_ATS_GC" => true | _ => false
end // end of [flag_is_ATS_GC]
val is_ATS_GC: intref = intref_make 0

fn flag_is_ATS_GCATS (flag: string): Bool = begin
  case+ flag of "-D_ATS_GCATS" => true | _ => false
end // end of [flag_is_ATS_GCATS]
val is_ATS_GCATS: intref = intref_make 0

fn flag_is_ATS_GCATS0 (flag: string): Bool = begin
  case+ flag of "-D_ATS_GCATS0" => true | _ => false
end // end of [flag_is_ATS_GCATS0]
val is_ATS_GCATS0: intref = intref_make 0

fn flag_is_ATS_gc (flag: string): Bool = begin
  case+ flag of "-D_ATS_gc" => true | _ => false
end // end of [flag_is_ATS_gc]
val is_ATS_gc: intref = intref_make 0

(* ****** ****** *)

fn flag_is_ATS_MULTITHREAD (flag: string): Bool =
  case+ flag of "-D_ATS_MULTITHREAD" => true | _ => false

val is_ATS_MULTITHREAD = intref_make 0
extern val "is_ATS_MULTITHREAD" = is_ATS_MULTITHREAD

(* ****** ****** *)

fn flag_is_ATS_DEBUG (flag: string): Bool = begin
  case+ flag of "-D_ATS_DEBUG" => true | _ => false
end // end of [flag_is_ATS_DEBUG]
val is_ATS_DEBUG: intref = intref_make 0

(* ****** ****** *)

fn flag_is_lats (flag: string): Bool =
  case+ flag of "-lats" => true | _ => false
val is_lats: intref = intref_make 0

(* ****** ****** *)

extern
fun atscc_outfile_name_make (basename: string): String
  = "atscc_outfile_name_make"

(* ****** ****** *)
  
fn atscc_argv_process {n:pos} {l:addr}
  (pf: !array_v (String, n, l) | n: int n, p: ptr l): Strlst(*param_c*) = let

fn* aux {i:nat | i <= n} ( // .<n-i,0>.
    pf: !array_v (String, n, l)
  | param_ats: Strlst, param_c: Strlst, i: int i
  ) :<cloptr1> Strlst(*param_c*) =
  if i < n then let
    val s = p[i]
  in
    case+ 0 of
    | _ when IATS_wait_is_set () => begin
        IATS_wait_clear (); aux (pf | s :: param_ats, param_c, i+1)
      end // end of [_ when ...]
    | _ when string_is_flag s => begin
        aux_flag (pf | param_ats, param_c, i, s)
      end // end of [_ when ...]
    | _ => begin
        aux_file (pf | param_ats, param_c, i, s)
      end // end of [_]
  end else if intref_get is_objcode_only > 0 then let
    val param_c = strlst_reverse param_c
    val _IATSHOME = "-I" + ATSHOME_dir
    val param_c = _IATSHOME :: param_c
    val _Iruntime_global = "-I" + runtime_global
    val param_c = _Iruntime_global :: param_c
  in
    param_c
  end else let
    val param_c = (case+ 0 of
      | _ when intref_get is_ATS_GC > 0 => "-lgc" :: param_c
      | _ when intref_get is_ATS_GCATS > 0 => let
          val is_mt = intref_get is_ATS_MULTITHREAD > 0
          val gcobj_local =
            (if is_mt then "GCATS/gc_mt.o" else "GCATS/gc.o") : string
          val gcobj_global: string = runtime_global + gcobj_local
        in
          gcobj_global :: param_c
        end // end of [ATS_GCATS]
      | _ when intref_get is_ATS_GCATS0 > 0 => let
          val gc_o = runtime_global + "GCATS0/gc.o" in gc_o :: param_c
        end // end of [ATS_GCATS0]
      | _ when intref_get is_ATS_gc > 0 => let
          val is_mt = intref_get is_ATS_MULTITHREAD > 0
          val gcobj_local =
            (if is_mt then "gc/gc_mt.o" else "gc/gc.o") : string
          val gcobj_global: string = runtime_global + gcobj_local
        in
          gcobj_global :: param_c
        end // end of [ATS_gc]
      | _ => param_c
    ) : Strlst // end of [val]
    val param_c = (
      if intref_get is_lats > 0 then param_c else "-lats" :: param_c
    ) : Strlst
    val param_c = strlst_reverse param_c
    val ats_prelude_c = runtime_global + "ats_prelude.c"
    val param_c = ats_prelude_c :: param_c
    val _Latslib_global = "-L" + atslib_global
    val param_c = _Latslib_global :: param_c
    val _Iruntime_global = "-I" + runtime_global
    val param_c = _Iruntime_global :: param_c
    val _IATSHOME = "-I" + ATSHOME_dir
    val param_c = _IATSHOME :: param_c
  in
    param_c (* Strlst *)
  end // end of [aux]

and aux_flag {i:nat | i < n} // .<n-i-1,1>.
  (pf: !array_v (String, n, l) |
   param_ats: Strlst, param_c: Strlst, i: int i, flag: String)
  :<cloptr1> Strlst = begin case+ flag of
  | _ when flag_is_typecheck_only flag => let
      val () = intref_set (is_typecheck_only, 1)
      val param_ats = "--typecheck" :: param_ats
    in
      aux (pf | param_ats, param_c, i+1)
    end
  | _ when flag_is_compile_only flag => let
      val () = intref_set (is_compile_only, 1)
    in
      aux (pf | param_ats, param_c, i+1)
    end
  | _ when flag_is_objcode_only flag => let
      val () = intref_set (is_objcode_only, 1)
    in
      aux (pf | param_ats, flag :: param_c, i+1)
    end
  | _ when flag_is_version flag => let
      val () = atscc_version ()
    in
      aux (pf | param_ats, flag :: param_c, i+1)
    end
  | _ when flag_is_ATS_GC flag => let
      val () = intref_set (is_ATS_GC, 1)
    in
      aux (pf | param_ats, flag :: param_c, i+1)
    end
  | _ when flag_is_ATS_GCATS flag => let
      val () = intref_set (is_ATS_GCATS, 1)
    in
      aux (pf | param_ats, flag :: param_c, i+1)
    end
  | _ when flag_is_ATS_GCATS0 flag => let
      val () = intref_set (is_ATS_GCATS0, 1)
    in
      aux (pf | param_ats, flag :: param_c, i+1)
    end
  | _ when flag_is_ATS_gc flag => let
      val () = intref_set (is_ATS_gc, 1)
    in
      aux (pf | param_ats, flag :: param_c, i+1)
    end
  | _ when flag_is_ATS_MULTITHREAD flag => let
      val () = intref_set (is_ATS_MULTITHREAD, 1)
    in
      aux (pf | param_ats, flag :: param_c, i+1)
    end
  | _ when flag_is_lats flag => let
      val () = intref_set (is_lats, 1)
    in
      aux (pf | param_ats, flag :: param_c, i+1)
    end
  | _ when flag_is_ATS_DEBUG flag => let
      val param_ats = "--debug=1" :: param_ats
    in
      aux (pf | param_ats, flag :: param_c, i+1)
    end
  | _ when flag_is_IATSdir flag => let
      val param_ats = flag :: param_ats
      val dir = IATS_extract flag; val () = begin
        if stropt_is_some dir then () else IATS_wait_set ()
      end // end of [if]
    in
      aux (pf | param_ats, param_c, i+1)
    end // end of [_ when ...]
  | _ => aux (pf | param_ats, flag :: param_c, i+1)
end // end of [aux_flag]

and aux_file {i:nat | i < n} // .<n-i-1,1>.
  (pf: !array_v (String, n, l) |
   param_ats: Strlst, param_c: Strlst, i: int i, file: String)
  :<cloptr1> Strlst = let
  val sfx = suffix_of_filename file
  val flag_stadyn = (
    if stropt_is_none sfx then ~1 else begin
      case stropt_unsome sfx of "sats" => 0 | "dats" => 1 | _ => ~1
    end
  ) : int
  val flag_debug = (if intref_get (is_ATS_DEBUG) > 0 then 1 else 0): int
in
  if flag_stadyn >= 0 then
    if intref_get (is_typecheck_only) > 0 then let
      val () = typecheck_file (flag_stadyn, param_ats, file)
    in
      aux (pf | param_ats, param_c, i+1)
    end else let 
      val basename = basename_of_filename file
      val outfile_c = atscc_outfile_name_make basename
      val () = ccomp_file_to_file (flag_stadyn, param_ats, file, outfile_c)
      val param_c = outfile_c :: param_c
    in
      aux (pf | param_ats, param_c, i+1)
    end
  else begin
    aux (pf | param_ats, file :: param_c, i+1)
  end
end // end of [aux_file]

in
  aux (pf | nil (*param_ats*), nil (*param_c*), 1)
end // end of [aux]

extern val "atscc_argv_process" = atscc_argv_process

(* ****** ****** *)

dynload "basics.dats"
dynload "atscc.dats"

implement main_prelude () = ()

(* ****** ****** *)

extern
fun __ats_main {n:pos} (argc: int n, argv: &(@[string][n])): void
  = "__ats_main"

implement main (argc, argv) = case+ argc of
  | 1 => let val cmd = argv.[0] in do_usage (basename_of_filename cmd) end
  | _ => __ats_main (argc, argv)
// end of [main]

(* ****** ****** *)

%{$

static int the_IATS_wait = 0 ;

ats_void_type IATS_wait_set () {
  the_IATS_wait = 1 ; return ;
}

ats_bool_type IATS_wait_is_set () {
  return (the_IATS_wait ? ats_true_bool : ats_false_bool) ;
}

ats_void_type IATS_wait_clear () {
  the_IATS_wait = 0 ; return ;
}

/* ****** ****** */

ats_bool_type
flag_is_IATSdir (ats_ptr_type s0) {
  char *s = (char*)s0 ;
  if (*s != '-') return ats_false_bool ;
  ++s ; if (*s != 'I') return ats_false_bool ;
  ++s ; if (*s != 'A') return ats_false_bool ;
  ++s ; if (*s != 'T') return ats_false_bool ;
  ++s ; if (*s != 'S') return ats_false_bool ;
  return ats_true_bool ; 
} /* end of [flag_is_IATSdir] */

ats_ptr_type
IATS_extract (ats_ptr_type s0) {
  int n ; char* s ;
  n = strlen ((char*)s0) ;
  n -= 5 ; if (n <= 0) return (ats_ptr_type)0 ;
  s = ats_malloc_gc (n + 1) ;
  memcpy (s, (char*)s0 + 5, n) ; s[n] = '\0' ;
  return s ;
} /* end of [IATS_extract] */

%}

(* ****** ****** *)

%{$

//

typedef ats_ptr_type ats_stropt_type ;
typedef ats_ptr_type ats_string_type ;

extern ats_ptr_type strlst_head_get(ats_ptr_type) ;
extern ats_ptr_type strlst_tail_get(ats_ptr_type) ;

extern ats_int_type strlst_length(ats_ptr_type) ;
extern ats_ptr_type strlst_reverse(ats_ptr_type) ;

//

extern ats_intref_type is_compile_only ;
extern ats_intref_type is_typecheck_only ;
extern ats_int_type inref_get(ats_intref_type) ;

ats_string_type
atscc_outfile_name_make (ats_string_type basename) {
  int n ; char c, *s ;
  n = strlen((char*)basename) ;
  s = (char*)ats_malloc_gc(n+3) ;
  s[n+2] = '\000' ; s[n+1] = 'c' ; s[n] = '.' ; --n ;
  while (n >= 0) {
    c = ((char*)basename)[n] ;
    if (c == '.') { s[n] = '_' ; --n ; break ; }
    s[n] = c ; --n ;
  }
  while (n >= 0) { s[n] = ((char*)basename)[n] ; --n ; }
  return s ;
} /* end of [atscc_outfile_name_make] */

ats_void_type
__ats_main (ats_int_type argc, ats_ptr_type argv) {
  int i, n ;
  ats_sum_ptr_type ss ;
  ats_ptr_type argv_new, p ; pid_t pid ; int status ;

  ss = ((ats_sum_ptr_type (*)(ats_int_type, ats_ptr_type))atscc_argv_process)(argc, argv) ;

  if (intref_get(is_compile_only) > 0) return ;
  if (intref_get(is_typecheck_only) > 0) return ;

  n = strlst_length(ss) ;
  argv_new = ats_malloc_ngc ((n+1)*sizeof(ats_string_type)+sizeof(ats_stropt_type)) ;
  p = argv_new ;

  // initialization for [argv_new]
  *((ats_string_type *)p) = "gcc" ;
  p = ((ats_string_type *)p) + 1 ;
  for (i = 0; i < n; ++i) {
    *((ats_string_type *)p) = strlst_head_get(ss) ;
    p = ((ats_string_type *)p) + 1 ; ss = strlst_tail_get(ss) ;
  } /* end of [for] */
  *((ats_stropt_type *)p) = (ats_stropt_type)0 ;

  // printf ("argv_new = ") ;
  for (i = 0; i <= n; ++i) {
    printf ("%s ", ((ats_string_type *)argv_new)[i]) ;
  } /* end of [for] */
  printf ("\n") ;

  pid = fork () ;
  if (pid < 0) {
    ats_exit_errmsg (errno, "Exit: [fork] failed.\n") ;
  } /* end of [if] */
  if (pid == 0) execvp ("gcc", argv_new) ; // this is the child
  wait (&status) ; // this is the parent
  if (status) {
    atspre_exit_prerrf (status, "Exit: [gcc] failed.\n") ;
  } /* end of [if] */
  return ;
} /* end of [__ats_main] */

%}

(* ****** ****** *)

(* end of [atscc_main.dats] *)
