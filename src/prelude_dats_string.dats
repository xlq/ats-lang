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

implement string_empty = "" // this requires dynamic loading

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

%{$

// a commonly used simple hash function

ats_uint_type atspre_string_hash_33 (ats_ptr_type s0)
{
  unsigned int hash_val ; unsigned char *s; int c;
  hash_val = 314159 ;

  s = (unsigned char*)s0 ;
  while (1) {
    c = *s ;
    if (!c) return hash_val ;
    hash_val = ((hash_val << 5) + hash_val) + c ;
    s += 1 ;
  }
}

%}

(* ****** ****** *)

%{$

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

(* end of [prelude_dats_string.dats] *)
