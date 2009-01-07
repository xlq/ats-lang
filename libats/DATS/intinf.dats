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
 * the  terms of the  GNU General Public License as published by the Free
 * Software Foundation; either version 2.1, or (at your option) any later
 * version.
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

// infinite precision integers based on the gmp package

(* ****** ****** *)

%{^

#include "libc/CATS/gmp.cats"

%}

(* ****** ****** *)

staload "libc/SATS/gmp.sats"
staload "libats/SATS/intinf.sats"

(* ****** ****** *)

assume intinf (i:int) = mpz_vt // [i] is a fake

(* ****** ****** *)

implement intinf_make (i) = let
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init_set (!p, i)
in
  @(pf_gc, pf_at | p)
end // end of [intinf_of_int1]

implement intinf_free (pf_gc, pf_at | p) =
  (mpz_clear (!p); ptr_free {Intinf} (pf_gc, pf_at | p))
// end of [intinf_free]

(* ****** ****** *)

implement fprint_intinf
  (pf | fil, intinf) = mpz_out_str (pf | fil, 10, intinf)
// end of [fprint_intinf]

implement print_intinf (intinf) = print_mac (fprint_intinf, intinf)

implement fprint_intinf_base
  (pf | fil, base, intinf) = mpz_out_str (pf | fil, base, intinf)
// end of [fprint_intinf_base]

implement print_intinf_base (base, intinf) = let
  val (pf_stdout | p_stdout) = stdout_get ()
  val () = fprint_intinf_base
    (file_mode_lte_w_w | !p_stdout, base, intinf)
  val () = stdout_view_set (pf_stdout | (*none*))
in
  // empty
end // end of [print_intinf_base]

(* ****** ****** *)

implement pred_intinf (intinf) = let
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_sub (!p, intinf, 1)
in
  @(pf_gc, pf_at | p)
end // end of [pred_intinf]

implement succ_intinf (intinf) = let
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_add (!p, intinf, 1)
in
  @(pf_gc, pf_at | p)
end // end of [succ_intinf]

(* ****** ****** *)

implement add_intinf_int (intinf, i) = let
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_add (!p, intinf, i)
in
  @(pf_gc, pf_at | p)
end // end of [add_intinf_int]

implement add_intinf_intinf (intinf1, intinf2) = let
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_add (!p, intinf1, intinf2)
in
  @(pf_gc, pf_at | p)
end // end of [add_intinf_intinf]

(* ****** ****** *)

implement sub_intinf_int (intinf, i) = let
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_sub (!p, intinf, i)
in
  @(pf_gc, pf_at | p)
end // end of [sub_intinf_int]

implement sub_intinf_intinf (intinf1, intinf2) = let
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_sub (!p, intinf1, intinf2)
in
  @(pf_gc, pf_at | p)
end // end of [sub_intinf_intinf]

(* ****** ****** *)

implement mul_int_intinf {m,n} (int, intinf) = let
  prval pf_mul = mul_make {m,n} ()
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_mul (!p, intinf, int)
in
  @(pf_mul | @(pf_gc, pf_at | p))
end // end of [mul_int_intinf]

implement mul_intinf_int {m,n} (intinf, int) = let
  prval pf_mul = mul_make {m,n} ()
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_mul (!p, intinf, int)
in
  @(pf_mul | @(pf_gc, pf_at | p))
end // end of [mul_intinf_int]

implement mul_intinf_intinf {m,n} (intinf1, intinf2) = let
  prval pf_mul = mul_make {m,n} ()
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_mul (!p, intinf1, intinf2)
in
  @(pf_mul | @(pf_gc, pf_at | p))
end // end of [mul_intinf_intinf]

(* ****** ****** *)

implement div_intinf_int {m,n} (intinf, i) = let
  prval [q,r:int] pf_mul =
    div_lemma {m,n} () where {
    extern praxi div_lemma {m,n:int | n > 0} ()
      : [q,r:int | 0 <= r; r < n] MUL (q, n, m-r)
  } // end of [prval]
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p)
  val ui = ulint_of_int i; val () = mpz_tdiv_q (!p, intinf, ui)
in
  #[q,r | @(pf_mul | @(pf_gc, pf_at | p))]
end // end of [div_intinf_int]

(* ****** ****** *)

(* end of [intinf.dats] *)
