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

#define ATS_DYNLOADFLAG 0 // loaded by [main_prelude]

(* ****** ****** *)

implement strbuf_v_split
  (pf_mul, pf_str) = split (pf_mul, pf_str) where {
  prfun split {m,n:nat} {i:nat | i <= n} {l:addr} {ofs:int} .<n>.
    (pf_mul: MUL (i, sizeof char, ofs), pf_str: strbuf_v (m, n, l))
    : (c1hars i @ l, strbuf_v (m-i, n-i, l+ofs)) =
    sif i == 0 then let
      prval () = mul_elim {0, sizeof char} (pf_mul)
    in
      @(array_v_nil {c1har} (), pf_str)
    end else let
      prval (pf1_at, pf2_stropt) = strbuf_v_uncons (pf_str)
      prval strbufopt_v_some pf2_str = pf2_stropt
      prval pf2_mul = mul_add_const {~1} (pf_mul)
      prval (pf1_res, pf2_res) = split {m-1,n-1} (pf2_mul, pf2_str)
    in
      (array_v_cons {c1har} (pf1_at, pf1_res), pf2_res)
    end // end of [sif]
  // end of [split]
} // end of [strbuf_v_split]

implement strbuf_v_unsplit
  (pf_mul, pf_buf, pf_str) = unsplit (pf_mul, pf_buf, pf_str) where {
  prfun unsplit {n1:nat} {m2,n2:nat} {l:addr} {ofs:int} .<n1>. (
      pf_mul: MUL (n1, sizeof char, ofs)
    , pf_buf: c1hars n1 @ l
    , pf_str: strbuf_v (m2, n2, l+ofs)
    ) : strbuf_v (n1+m2, n1+n2, l) =
    sif n1 == 0 then let
      prval () = mul_elim {0, sizeof char} (pf_mul)
      prval () = array_v_unnil {c1har} (pf_buf)
    in
      pf_str
    end else let
      prval pf2_mul = mul_add_const {~1} (pf_mul)
      prval (pf1_at, pf2_buf) = array_v_uncons {c1har} (pf_buf)
      prval pf2_res = unsplit {n1-1} (pf2_mul, pf2_buf, pf_str)
    in
      strbuf_v_cons (pf1_at, pf2_res)
    end // end of [sif]
  // end of [unsplit]
} // end of [strbuf_v_unsplit]

(* ****** ****** *)

%{^

static inline
ats_ptr_type
_string_alloc (const ats_int_type n) {
  char *p ;
  p = ATS_MALLOC(n+1); p[n] = '\000'; return p ;
} // end of [_string_alloc]

%}

(* ****** ****** *)

implement string_empty = "" // this requires dynamic loading

(* ****** ****** *)

implement string_make_list (cs) = let
  val n = loop (cs, 0) where {
    fun loop {i,j:nat} .<i>.
      (cs: list (char, i), j: int j):<> int (i+j) = case+ cs of
      | list_cons (_, cs) => loop (cs, j+1) | list_nil () => j
  } // end of [val]
in
  string_make_list_len (cs, n)
end // end of [string_make_list]

#define NUL '\000'

implement string_make_list_len (cs, n) = let
  val (pf_gc, pf_sb | p_sb) = _string_alloc n where {
    extern fun _string_alloc {n:nat} (n: int n)
      :<> [l:addr] (free_gc_v (n+1, l), strbuf (n+1, n) @ l | ptr l)
      = "_string_alloc"
  } // end of [val]
  val () = loop (!p_sb, n, 0, cs) where {
    fun loop {m,n:nat} {i,j:nat | i + j == n} .<n-i>.
      (buf: &strbuf (m, n), n: int n, i: int i, cs: list (char, j)):<> void =
      if i < n then let
        val+ list_cons (c, cs) = cs
        val [c:char] c = char1_of_char c
        val () = $effmask_all (if (c <> NUL) then () else begin
          prerr ("exit(ATS): a string cannot contain null characters in the middle.");
          prerr_newline (); exit (1)
        end) : [c <> NUL] void // end of [val]
      in
        strbuf_set_char_at (buf, i, c); loop (buf, n, i+1, cs)
      end else begin
        // loop exists
      end // end of [if]
  } // end of [val]
in
  string1_of_strbuf (pf_gc, pf_sb | p_sb)
end // end of [string_make_list_len]

(* ****** ****** *)

implement stringlst_concat (ss) = let
  val n0 = aux (ss, 0) where {
    fun aux {k:nat} .<k>.
      (ss: list (string, k), n: Nat):<> Nat = case+ ss of
      | list_cons (s, ss) => aux (ss, n + string0_length s) | list_nil () => n
    // end of [aux]
  } // end of [val n0]
  fun loop1 {m0,n0,i0,n,i:nat | i0 <= n0; i <= n} .<n0-i0>.
    (s0: &strbuf (m0, n0), n0: int n0, i0: int i0, s: string n, i: int i)
    :<> [i0: nat | i0 <= n0] int i0 = begin
    if string1_is_at_end (s, i) then i0 else begin
      if i0 < n0 then (s0[i0] := s[i]; loop1 (s0, n0, i0+1, s, i+1)) else i0
    end // end of [if]
  end // end of [loop1]
  fun loop2 {m0,n0,i0,k:nat | i0 <= n0} .<k>.
    (s0: &strbuf (m0, n0), n0: int n0, i0: int i0, ss: list (string, k))
    :<> void = begin case+ ss of
    | list_cons (s, ss) => let
        val s = string1_of_string0 s; val i0 = loop1 (s0, n0, i0, s, 0)
      in
        loop2 (s0, n0, i0, ss)
      end // end of [list_cons]
    | list_nil () => () // loop exists
  end // end of [loop2]
  val (pf_gc, pf_sb | p_sb) = _string_alloc n0 where {
    extern fun _string_alloc {n:nat} (n: int n)
      :<> [l:addr] (free_gc_v (n+1, l), strbuf (n+1, n) @ l | ptr l)
      = "_string_alloc"
  } // end of [val]
  val () = loop2 (!p_sb, n0, 0, ss)
in
  string1_of_strbuf (pf_gc, pf_sb | p_sb)
end // end of [stringlst_concat]

(* ****** ****** *)

implement string1_explode (s) = let
  fun loop {n,i:int | ~1 <= i; i < n} .<i+1>. (
      s: string n, i: int i, cs: list (char, n-i-1)
    ) :<> list (char, n) = begin
    if i >= 0 then loop (s, i-1, list_cons (s[i], cs)) else cs
  end // end of [loop]
in
  loop (s, length s - 1, list_nil ())
end // end of [string1_explode]

(* ****** ****** *)

%{$

// a commonly used simple hash function

ats_uint_type
atspre_string_hash_33 (ats_ptr_type s0) {
  unsigned int hash_val ; unsigned char *s; int c;
  hash_val = 314159 ;

  s = (unsigned char*)s0 ;
  while (1) {
    c = *s ;
    if (!c) return hash_val ;
    hash_val = ((hash_val << 5) + hash_val) + c ;
    s += 1 ;
  }
} /* atspre_string_hash_33 */

%}

(* ****** ****** *)

%{$

ats_ptr_type
atspre_string_make_char
  (const ats_int_type n, const ats_char_type c) {
  char *p ; 
  if (!c) { ats_exit_errmsg
    (1, "exit(ATS): [string_make_char] failed: null char.\n") ;
  } ;
  p = ATS_MALLOC(n+1) ; memset (p, c, n) ; p[n] = '\000' ;
  return p ;
} /* atspre_string_make_char */

/* ****** ****** */

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

%}

(* ****** ****** *)

(* end of [string.dats] *)
