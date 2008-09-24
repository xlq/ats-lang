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
 * along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
 * Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

// July 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

(*
 *
 * The tagged states of a DFA are stored in a binary tree constructed
 * according to the randomized binary search tree algorithm.
 *
 *)

//

%{^

#include "libc/CATS/random.cats"

%}

//

staload "top.sats"

//

dataviewtype states (int) =
  | STSnil (0)
  | {sl,sr:nat} STScons(1+sl+sr) of
       (int (1+sl+sr), int, intset_t, states sl, states sr)

assume states_t = [n:nat] states n

(* ****** ****** *)

implement states_nil = STSnil ()

implement states_free (sts): void = let
fun free {s:nat} .<s>. (sts: states s): void =
  case+ sts of
    | ~STScons (_, _, _, sts_l, sts_r) => (free sts_l; free sts_r)
    | ~STSnil () => ()
in
  free sts
end // end of [states_free]

(* ****** ****** *)

implement states_find (sts, ns0): int = let
fun loop {s:nat} .<s>. (sts: !states s, ns0: intset_t): int =
  case+ sts of
  | STScons (s, tag, ns, !sts_l, !sts_r) => begin
    case+ compare (ns0, ns) of
    | ~1 => let val ans = loop (!sts_l, ns0) in fold@ sts; ans end
    |  1 => let val ans = loop (!sts_r, ns0) in fold@ sts; ans end
    |  0 => (fold@ sts; tag)
    end
  | STSnil () => (fold@ sts; ~1)
in
  loop (sts, ns0)
end // end of [states_find]

(* ****** ****** *)

fn states_size {s:nat} (sts: !states s): int s = begin case+ sts of
  | STScons (s, _, _, _, _) => (fold@ sts; s) | STSnil () => (fold@ sts; 0)
end // end of [states_size]

//

#define i2d double_of_int
staload Rand = "libc/SATS/random.sats"

fn dice {m,n:int | m > 0; n > 0} (m: int m, n: int n): bool =
  let val r = $Rand.drand48 () in i2d (m + n) * r < i2d m end

//

implement states_insert (sts, tag0, ns0) = let
fun insert_at_root {s:nat} .<s>.
  (sts: states s, tag0: int, ns0: intset_t): states (s+1) =
  case+ sts of
  | STScons (!s, tag, ns, !sts_l, !sts_r) => begin
      if compare (ns0, ns) >= 0 then let
        val sts_r_new = insert_at_root (!sts_r, tag0, ns0)
        val+ STScons (!sr, tag_r, ns_r, !sts_rl, !sts_rr) = sts_r_new
        val s_v = !s; val srr_v = states_size !sts_rr
      in
        !sts_r := !sts_rl; !s := s_v - srr_v; fold@ sts;
        !sts_rl := sts; !sr := s_v + 1; fold@ sts_r_new; sts_r_new
      end else let
        val sts_l_new = insert_at_root (!sts_l, tag0, ns0)
        val+ STScons (!sl, tag_l, ns_l, !sts_ll, !sts_lr) = sts_l_new
        val s_v = !s; val sll_v = states_size !sts_ll
      in
        !sts_l := !sts_lr; !s := s_v - sll_v; fold@ sts;
        !sts_lr := sts; !sl := s_v + 1; fold@ sts_l_new; sts_l_new
      end
    end
  | ~STSnil () => STScons (1, tag0, ns0, STSnil (), STSnil ())

fun insert_random {s:nat} .<s>.
  (sts: states s, tag0: int, ns0: intset_t): states (s+1) =
  case+ sts of
  | STScons (!s as s_v, tag, ns, !sts_l, !sts_r) =>
    if dice (1, s_v) then begin
      fold@ sts; insert_at_root (sts, tag0, ns0)
    end else begin
      if compare (ns0, ns) >= 0 then begin
        !sts_r := insert_random (!sts_r, tag0, ns0);
        !s := s_v + 1; fold@ sts; sts
      end else begin
        !sts_l := insert_random (!sts_l, tag0, ns0);
        !s := s_v + 1; fold@ sts; sts
      end
    end
  | ~STSnil () => STScons (1, tag0, ns0, STSnil (), STSnil ())
in
  sts := insert_random (sts, tag0, ns0)
end // end of [states_insert]

(* ****** ****** *)

implement states_foreach_and_free {v} (pf | f, sts) = let

viewtypedef cloptr_t = (!v | int, intset_t) -<cloptr1> void
fun aux {s:nat} .<s>. (pf: !v | f: !cloptr_t, sts: states s): void =
  case+ sts of
  | ~STScons (s, tag, ns, sts_l, sts_r) => begin
      f (pf | tag, ns); aux (pf | f, sts_l); aux (pf | f, sts_r)
    end
  | ~STSnil () => ()
in
  aux (pf | f, sts)
end // end of [states_foreach_and_free]

(* ****** ****** *)

(* end of [states.dats] *)
