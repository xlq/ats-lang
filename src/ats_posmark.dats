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

// November 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

%{^

#include "libc/CATS/stdio.cats"
#include "libc/CATS/stdlib.cats"

%}

// staload "libc/SATS/stdio.sats"

extern fun fopen_exn {m:file_mode}
  (s: string, m: file_mode m): [l:addr] (FILE m @ l | ptr l)
  = "atslib_fopen_exn"

extern fun fclose_exn {m:file_mode} {l:addr}
  (pf: FILE m @ l | p: ptr l):<!exnref> void
  = "atslib_fclose_exn"

extern fun fgetc_err {m:file_mode}
  (pf: file_mode_lte (m, r) | f: &FILE m): int
  = "atslib_fgetc_err"

extern fun fputc_exn {m:file_mode}
  (pf: file_mode_lte (m, w) | c: char, f: &FILE m): void
  = "atslib_fputc_exn"

// staload "libc/SATS/stdlib.sats"

extern fun qsort {a:viewt@ype} {n:nat} {f:eff} (
  base: &(@[a][n]), nmemb: int n, size: sizeof_t a, compar: (&a, &a) -<f> int
) : void = "atslib_qsort"

(* ****** ****** *)

staload "ats_array.sats"
staload "ats_posmark.sats"

(* ****** ****** *)

staload _(*anonymous*) = "ats_array.dats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

datatype posmark = // 0/1 : begin/end
  | PMnone
  | PMcomment of int
  | PMextern of int
  | PMkeyword of int
  | PMneuexp of int
  | PMstaexp of int
  | PMprfexp of int

(* ****** ****** *)

val the_posmark_flag : ref int = ref_make_elt<int> 0
val the_posmarklst : ref (List @(lint, posmark)) =
  ref_make_elt (list_nil ())

(* ****** ****** *)

#define NPOSMARK 64
fn int_of_posmark (pm: posmark): int =
  case+ pm of
  | PMnone () => 0
  | PMcomment i => if i > 0 then 1 else NPOSMARK-1
  | PMextern i => if i > 0 then 2 else NPOSMARK-2
  | PMkeyword i => if i > 0 then 3 else NPOSMARK-3
  | PMneuexp  i => if i > 0 then 4 else NPOSMARK-4
  | PMstaexp  i => if i > 0 then 4 else NPOSMARK-5
  | PMprfexp  i => if i > 0 then 5 else NPOSMARK-6

fn compare_posmark_posmark (pm1: posmark, pm2: posmark): Sgn =
  compare (int_of_posmark pm1, int_of_posmark pm2)

(* ****** ****** *)

local

assume posmark_token = unit_v

in

implement posmark_initiate () = let
  val () = !the_posmark_flag := 1
  val () = !the_posmarklst := list_nil ()
in
  (unit_v () | ())
end

// prevent memory leak!
implement posmark_terminate (pf | (*none*)) =
  let prval unit_v () = pf in
    !the_posmark_flag := 0; !the_posmarklst := list_nil ()
  end

end // end of [local]

(* ****** ****** *)

fn posmark_insert (p: lint, pm: posmark): void = begin
  if !the_posmark_flag > 0 then begin
    !the_posmarklst := list_cons ((p, pm), !the_posmarklst)
  end
end // end of [posmark_insert]

implement posmark_insert_comment_beg (p) =
  posmark_insert (p, PMcomment 0)

implement posmark_insert_comment_end (p) =
  posmark_insert (p, PMcomment 1)

implement posmark_insert_extern_beg (p) =
  posmark_insert (p, PMextern 0)

implement posmark_insert_extern_end (p) =
  posmark_insert (p, PMextern 1)

implement posmark_insert_keyword_beg (p) =
  posmark_insert (p, PMkeyword 0)

implement posmark_insert_keyword_end (p) =
  posmark_insert (p, PMkeyword 1)

implement posmark_insert_neuexp_beg (p) =
  posmark_insert (p, PMneuexp 0)

implement posmark_insert_neuexp_end (p) =
  posmark_insert (p, PMneuexp 1)

implement posmark_insert_staexp_beg (p) =
  posmark_insert (p, PMstaexp 0)

implement posmark_insert_staexp_end (p) =
  posmark_insert (p, PMstaexp 1)

implement posmark_insert_prfexp_beg (p) =
  posmark_insert (p, PMprfexp 0)

implement posmark_insert_prfexp_end (p) =
  posmark_insert (p, PMprfexp 1)

(* ****** ****** *)

fn posmarklst_sort
  (ppms: List @(lint, posmark)): List_vt @(lint, posmark) = let

typedef ppm = @(lint, posmark)

fn cmp (x1: &ppm, x2: &ppm): Sgn = begin
  let val x10 = x1.0 and x20 = x2.0 in
    if x10 < x20 then ~1 else begin
      (if x10 > x20 then 1 else compare_posmark_posmark (x1.1, x2.1))
    end // end of [if]
  end // end of [let]
end // end of [cmp]

fun loop {n,i:int | 0 <= i + 1; i + 1 <= n}
  (A: &(@[ppm][n]), i: int i, res: list_vt (ppm, n-i-1))
  : list_vt (ppm, n) =
  if i >= 0 then begin
    loop (A, i-1, list_vt_cons (A.[i], res))
  end else begin
    res // return value
  end

val n = aux (ppms, 0) where {
  fun aux {i,j:nat} (ppms: list (ppm, i), j: int j): int (i+j) =
    case+ ppms of list_cons (_, ppms) => aux (ppms, j+1) | list_nil () => j
} // end of where
val (pf_gc, pf_arr | p_arr) = array_ptr_make_lst<ppm> (n, ppms)
val () = qsort {ppm} (!p_arr, n, sizeof<ppm>, cmp)
val res = loop (!p_arr, n-1, list_vt_nil ())
val () = array_ptr_free {ppm} (pf_gc, pf_arr | p_arr)

in

res

end // end of [posmarklst_sort]
  
(* ****** ****** *)

// color= gray
#define COMMENT_FONT_BEG "<FONT COLOR=\"#787878\">"
#define COMMENT_FONT_END "</FONT>"

// color= brown
#define EXTERN_FONT_BEG "<FONT COLOR=\"#A52A2A\">"
#define EXTERN_FONT_END "</FONT>"

// color= black
#define KEYWORD_FONT_BEG "<FONT COLOR=\"#000000\">"
#define KEYWORD_FONT_END "</FONT>"

// color= pink
#define NEUEXP_FONT_BEG "<FONT COLOR=\"#800080\">"
#define NEUEXP_FONT_END "</FONT>"

// color= blue
#define STAEXP_FONT_BEG "<FONT COLOR=\"#0000FF\">"
#define STAEXP_FONT_END "</FONT>"

// color= red
#define DYNEXP_FONT_BEG "<FONT COLOR=\"#E80000\">"
#define DYNEXP_FONT_END "</FONT>"

// color= green
#define PRFEXP_FONT_BEG "<FONT COLOR=\"#009000\">"
#define PRFEXP_FONT_END "</FONT>"

// color= light gray
#define POSMARK_FILE_BEG "<BODY BGCOLOR=\"#E0E0E0\" TEXT=\"#E80000\"><PRE>"
#define POSMARK_FILE_ENG "</PRE></BODY>"

fn posmark_process_htm
  (fil_d: &FILE w, pm: posmark): void = begin case+ pm of
  | PMnone () => ()
  | PMcomment i => begin
      if i = 0 then begin
        fprint1_string (file_mode_lte_w_w | fil_d, COMMENT_FONT_BEG)
      end else begin
        fprint1_string (file_mode_lte_w_w | fil_d, COMMENT_FONT_END)
      end
    end // end of [PMcomment]
  | PMextern i => begin
      if i = 0 then begin
        fprint1_string (file_mode_lte_w_w | fil_d, EXTERN_FONT_BEG)
      end else begin
        fprint1_string (file_mode_lte_w_w | fil_d, EXTERN_FONT_END)
      end
    end // end of [PMextern]
  | PMkeyword i => begin
      if i = 0 then begin
        fprint1_string (file_mode_lte_w_w | fil_d, KEYWORD_FONT_BEG)
      end else begin
        fprint1_string (file_mode_lte_w_w | fil_d, KEYWORD_FONT_END)
      end
    end // end of [PMkeyword]
  | PMneuexp i => begin
      if i = 0 then begin
        fprint1_string (file_mode_lte_w_w | fil_d, NEUEXP_FONT_BEG)
      end else begin
        fprint1_string (file_mode_lte_w_w | fil_d, NEUEXP_FONT_END)
      end
    end // end of [PMneuexp]
  | PMstaexp i =>  begin
      if i = 0 then begin
        fprint1_string (file_mode_lte_w_w | fil_d, STAEXP_FONT_BEG)
      end else begin
        fprint1_string (file_mode_lte_w_w | fil_d, STAEXP_FONT_END)
      end
    end // end of [PMstaexp]
  | PMprfexp i =>  begin
      if i = 0 then begin
        fprint1_string (file_mode_lte_w_w | fil_d, PRFEXP_FONT_BEG)
      end else begin
        fprint1_string (file_mode_lte_w_w | fil_d, PRFEXP_FONT_END)
      end
    end // end of [PMprfexp]
end // end of [posmark_process_htm]

fn fputc_html {m:file_mode}
  (pf: file_mode_lte (m, w) | c: char, out: &FILE m)
  : void = begin case+ c of
    | '<' => fprint1_string (pf | out, "&lt;")
    | '>' => fprint1_string (pf | out, "&gt;")
    | '&' => fprint1_string (pf | out, "&amp;")
    | _ => fputc_exn (pf | c, out)
end // end of [fputc_html]

fn posmark_file_file
  (proc: (&FILE w, posmark) -<fun1> void, fil_s: &FILE r, fil_d: &FILE w)
  : void = let
  typedef ppm =  @(lint, posmark)

  fun lpfin1
    (fil_s: &FILE r, fil_d: &FILE w, pm: posmark, ppms: List_vt ppm)
    :<cloptr1> void = let
    val () = proc (fil_d, pm)
  in
    case+ ppms of
    | ~list_vt_cons (ppm, ppms) => lpfin1 (fil_s, fil_d, ppm.1, ppms)
    | ~list_vt_nil () => ()
  end // end of [lpfin1]

  fun lpfin2 (fil_s: &FILE r, fil_d: &FILE w): void = let
    val c = fgetc_err (file_mode_lte_r_r | fil_s)
  in
    if (c >= 0) then begin
      fputc_html (file_mode_lte_w_w | char_of_int c, fil_d);
      lpfin2 (fil_s, fil_d)
    end
  end // end of [lpfin2]

  fn* loop1
    (fil_s: &FILE r, fil_d: &FILE w,
     i: lint, p: lint, pm: posmark, ppms: List_vt ppm)
    :<cloptr1> void = let
    val c = fgetc_err (file_mode_lte_r_r | fil_s)
  in
    if (c >= 0) then begin
      loop2 (fil_s, fil_d, i, p, pm, ppms, c)
    end else begin
      lpfin1 (fil_s, fil_d, pm, ppms)
    end
  end // end of [loop1]

  and loop2
    (fil_s: &FILE r, fil_d: &FILE w,
     i: lint, p: lint, pm: posmark, ppms: List_vt ppm, c: int)
    :<cloptr1> void = begin
    if i < p then begin
      fputc_html (file_mode_lte_w_w | char_of_int c, fil_d);
      loop1 (fil_s, fil_d, succ i, p, pm, ppms)
    end else let
      val () = proc (fil_d, pm)
    in
      case+ ppms of
      | ~list_vt_cons (ppm, ppms) => begin
          loop2 (fil_s, fil_d, i, ppm.0, ppm.1, ppms, c)
        end
      | ~list_vt_nil () => begin
          fputc_html (file_mode_lte_w_w | char_of_int c, fil_d);
          lpfin2 (fil_s, fil_d)
        end
    end
  end // end of [loop2]

  val lint0 = lint_of_int 0
  val ppms = posmarklst_sort !the_posmarklst
in
  fprint1_string (file_mode_lte_w_w | fil_d, POSMARK_FILE_BEG);
  loop1 (fil_s, fil_d, lint0, lint0, PMnone (), ppms);
  fprint1_string (file_mode_lte_w_w | fil_d, POSMARK_FILE_ENG);
  fprint1_newline (file_mode_lte_w_w | fil_d);
end // end of [posmark_file_file]

(* ****** ****** *)

extern fun posmark_htmlfilename_make (basename: string): string
  = "posmark_htmlfilename_make"

implement posmark_file_make_htm (basename): void = let
  val htmlfilename = posmark_htmlfilename_make (basename)
  val file_mode_r = $extval (file_mode r, "\"r\"")
  val file_mode_w = $extval (file_mode w, "\"w\"")
  val (pf_in | p_in) = fopen_exn (basename, file_mode_r)
  val (pf_out | p_out) = fopen_exn (htmlfilename, file_mode_w)
  val () = posmark_file_file (posmark_process_htm, !p_in, !p_out)
in
  fclose_exn (pf_out | p_out); fclose_exn (pf_in | p_in)
end // end of [posmark_file_make_htm]

%{$

ats_ptr_type
posmark_htmlfilename_make (ats_ptr_type basename) {
  int n ; char c, *s ;
  n = strlen((char *)basename) ;
  s = (char*)ATS_MALLOC (n+6) ;
  s[n+5] = '\000' ;
  s[n+4] = 'l'; s[n+3] = 'm' ; s[n+2] = 't' ; s[n+1] = 'h' ;
  s[n] = '.' ; --n ;
  while (n >= 0) {
    c = ((char *)basename)[n] ;
    if (c == '.') { s[n] = '_' ; --n ; break ; }
    s[n] = c ; --n ;
  }
  while (n >= 0) { s[n] = ((char *)basename)[n] ; --n ; }
  return s ;
}

%}

(* ****** ****** *)

(* end of [ats_posmark.sats] *)
