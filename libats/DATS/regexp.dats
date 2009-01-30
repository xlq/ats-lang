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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

// some basic IO operations

(* ****** ****** *)

staload "libats/SATS/regexp.sats"

(* ****** ****** *)

#define i2sz size1_of_int1
#define sz2i int1_of_size1

(* ****** ****** *)

%{$

pcre *atslib_regexp_compile_exn
  (ats_ptr_type pattern) {
  const char *errptr ; int erroffset ; pcre *result ;
  result = pcre_compile (
    (char*)pattern
  , 0 /* option bits */
  , &errptr, &erroffset
  , (unsigned char*)0 /* tableptr */
  ) ; // end of [pcre_compile]

  if (!result) {
    fprintf (stderr, "Exit: [pcre_compile] failed: %s\n", errptr) ;
    exit (1) ;
  } // end of [if]

  return result ;
} /* end of [atslib_regexp_compile_exn] */

%}

(* ****** ****** *)

implement test_regexp_match_str (re, str) = let
  val str = string1_of_string (str)
  val len = string_length (str); val len = sz2i (len)
in
  test_regexp_match_str_len_ofs (re, str, len, 0(*ofs*))
end // end of [test_regexp_match_str]

(* ****** ****** *)

%{$

ats_bool_type atslib_test_regexp_match_str_len_ofs
  (ats_ptr_type re, ats_ptr_type str, ats_int_type len, ats_int_type ofs) {
  int result ;
  result = pcre_exec (
    (pcre*)re
  , (pcre_extra*)0 /* [re] is not studied */
  , (char*)str, len, ofs
  , 0 /* option bits */
  , (int*)0 /* ovector */
  , 0 /* ovecsize */
  ) ; // end of [pcre_exec]

  if (result >= 0) return ats_true_bool ;

  switch (result) {
  case PCRE_ERROR_NOMATCH: return ats_false_bool ;
  default: fprintf
    (stderr, "exit(ATS): [test_regexp_match_str_len_ofs] failed\n"); exit (1);
  } /* end of [switch] */

  return ats_false_bool ; /* deadcode */
} /* end of [atslib_test_regexp_match_str_len_ofs] */

%}

(* ****** ****** *)

%{^

static inline
ats_int_type
atslib_string_split_regexp_search (
  ats_ptr_type re
, ats_ptr_type str
, ats_int_type len
, ats_int_type ofs
, ats_ptr_type ofsvec
) {
  int result ;
  result = pcre_exec (
    (pcre*)re
  , (pcre_extra*)0 /* [re] is not study */
  , (char*)str, len, ofs
  , 0 /* option bits */
  , (int*)ofsvec /* ovector */
  , 3 /* ovecsize */
  ) ; // end of [pcre_exec]

  return result ;
} /* end of [atslib_string_split_regexp_search] */

%}

implement string_split_regexp (str, re) = let
  extern fun search {n,i:nat | i < n} {l:addr} (
      pf_arr: ! @[int?][3] @ l >> @[int][3] @ l
    | re: REGEXPref, s0: string n, n: int n, i: int i, p: ptr l
    ) :<1,~ref> int
    = "atslib_string_split_regexp_search"

  fun loop {n,i:nat | i <= n} {l:addr} (
      pf_gc: free_gc_v (int, 3, l), pf_arr: @[int?][3] @ l
    | re: REGEXPref, s0: string n, n: int n, i: int i, p: ptr l
    ) :<1,~ref> stream_con string = case+ 0 of
    | _ when (i < n) => let
        val rc = search (pf_arr | re, s0, n, i, p)
      in
        case+ rc of
        | _ when rc >= 0 => let
            val i1 = int1_of !p.[0] and i2 = int1_of !p.[1]
            val () = assert (i <= i1)
            val () = assert (i1 <= i2)
            val () = assert (i2 <= n)
            val st = i2sz i and ln = i2sz (i1 - i)
            val s = string_make_substring (s0, st, ln)
          in
            stream_cons (s, $delay loop (pf_gc, pf_arr | re, s0, n, i2, p))
          end // end of [_ when rc >= 0]
        | _ => let
            val st = i2sz i and ln = i2sz (n - i)
            val s = string_make_substring (s0, st, ln)
          in
            stream_cons (s, $delay loop (pf_gc, pf_arr | re, s0, n, n, p))
          end // end of [_]
      end // end of [_ when (i < n)]
    | _ (* i = n *) => let
        val () = array_ptr_free {int} (pf_gc, pf_arr | p)
      in
        stream_nil ()
      end // end of [_]

  val _3 = i2sz 3
  val s0 = string1_of_string str
  val n = string_length s0; val n = sz2i (n)
  val (pf_gc, pf_arr | p) = array_ptr_alloc_tsz {int} (_3, sizeof<int>)
in
  $delay loop (pf_gc, pf_arr | re, s0, n, 0, p)
end // end of [string_split_regexp]

(* ****** ****** *)

val () = initialize () where {
  extern fun initialize (): void = "atslib_libats_regexp_initialize"
}

(* ****** ****** *)

%{$

ats_void_type atslib_libats_regexp_initialize () {
  pcre_malloc = (void *(*)(size_t))ats_malloc_gc ;
  pcre_free = (void (*)(void*))ats_free_gc ;
  pcre_stack_malloc = (void *(*)(size_t))ats_malloc_gc ;
  pcre_stack_free = (void (*)(void*))ats_free_gc ;
  return ;  
} /* end of [atslib_libats_regexp_initialize] */

%}

(* ****** ****** *)

(* end of [regexp.dats] *)
