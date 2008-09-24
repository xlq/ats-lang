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

#if VERBOSE_PRELUDE #then

#print "Loading [memory.sats] starts!\n"

#endif

(* ****** ****** *)

viewdef bytes_v (n:int, l:addr) = @[byte][n] @ l

// two axioms
praxi to_bytes_v : {a:viewtype} {l:addr} a? @ l -<prf> bytes_v (sizeof a, l)
praxi of_bytes_v : {a:viewtype} {l:addr} bytes_v (sizeof a, l) -<prf> a? @ l

prval array_v_of_bytes_v : {a:viewtype} {n:nat} {l:addr} {nsz:int}
  (MUL (n, sizeof a, nsz), bytes_v (nsz, l)) -<prf> @[a][n] @ l

(* ****** ****** *)

fun gc_init (): void = "ats_gc_init"

(* ****** ****** *)

// the following functions are implemented in ats_memory.h"

fun malloc_ngc {n:nat} (n: int n)
  :<> [l:addr] (free_ngc_v l, bytes_v (n, l) | ptr l)
  = "ats_malloc_ngc"

fun calloc_ngc {a:viewtype} {n:nat}
  (n: int n, tsz: sizeof_t a):<> [l:addr] (free_ngc_v l, @[a?][n] @ l | ptr l)
  = "ats_calloc_ngc"

fun free_ngc {n:nat} {l:addr}
  (_: free_ngc_v l, _: bytes_v (n, l) | p: ptr l):<> void
  = "ats_free_ngc"

fun realloc_ngc {n0,n:nat} {l0:addr}
  (_: free_ngc_v l0, _: bytes_v (n0, l0) | _: ptr l0, _: int n)
  :<> [l:addr] (free_ngc_v l, bytes_v (n, l) | ptr l)
  = "ats_realloc_ngc"

(* ****** ****** *)

fun gc_chunk_count_limit_get (): int
  = "ats_gc_chunk_count_limit_get"

fun gc_chunk_count_limit_set (n: int): void
  = "ats_gc_chunk_count_limit_set"

fun gc_chunk_count_limit_max_get (): int
  = "ats_gc_chunk_count_limit_max_get"

fun gc_chunk_count_limit_max_set (n: int): void
  = "ats_gc_chunk_count_limit_max_set"

(* ****** ****** *)

fun malloc_gc {n:nat}
  (n: int n):<> [l:addr] (free_gc_v l, bytes_v (n, l) | ptr l)
  = "ats_malloc_gc"

fun calloc_gc {a:viewtype} {n:nat}
  (n: int n, tsz: sizeof_t a):<> [l:addr] (free_gc_v l, @[a?][n] @ l | ptr l)
  = "ats_calloc_gc"

fun free_gc {n:nat} {l:addr}
  (_: free_gc_v l, _: bytes_v (n, l) | p: ptr l):<> void
  = "ats_free_gc"

fun realloc_gc {n0,n:nat} {l0:addr}
  (_: free_gc_v l0, _: bytes_v (n0, l0) | _: ptr l0, _: int n)
  :<> [l:addr] (free_gc_v l, bytes_v (n, l) | ptr l)
  = "ats_realloc_gc"


(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [memory.sats] finishes!\n"

#endif

(* end of [memory.sats] *)
