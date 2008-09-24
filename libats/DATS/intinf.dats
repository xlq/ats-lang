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

assume intinf (i:int) = (* [i] is a fake *)
  [l:addr] (free_gc_v l, mpz_vt @ l | ptr l)

implement intinf_of_int1 (i) = let
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init_set (!p, i)
in
  @(pf_gc, pf_at | p)
end // end of [intinf_of_int1]

implement intinf_free (intinf) = let
  val @(pf_gc, pf_at | p) = intinf
in
  mpz_clear (!p); ptr_free (pf_gc, pf_at | p)
end

(* ****** ****** *)

implement fprint_intinf (pf | fil, intinf) = let
  prval pf_at = intinf.1
in
  mpz_out_str (pf | fil, 10, !(intinf.2));
  intinf.1 := pf_at
end

implement print_intinf (intinf) = print_mac (fprint_intinf, intinf)

implement fprint_intinf_base (pf | fil, base, intinf) = let
  prval pf_at = intinf.1
in
  mpz_out_str (pf | fil, base, !(intinf.2));
  intinf.1 := pf_at
end

implement print_intinf_base (base, intinf) =
  let val (pf_out | p_out) = stdout_get () in
    fprint_intinf_base (file_mode_lte_w_w | !p_out, base, intinf);
    stdout_view_set (pf_out | (*none*))
  end

(* ****** ****** *)

implement pred_intinf (intinf) = let
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p)
  prval pf1_at = intinf.1
  val () = mpz_sub (!p, !(intinf.2), 1)
  prval () = intinf.1 := pf1_at
in
  @(pf_gc, pf_at | p)
end // end of [pred_intinf]

implement succ_intinf (intinf) = let
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p)
  prval pf1_at = intinf.1
  val () = mpz_add (!p, !(intinf.2), 1)
  prval () = intinf.1 := pf1_at
in
  @(pf_gc, pf_at | p)
end // end of [succ_intinf]

//

implement add_intinf_int (intinf, i) = let
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p)
  prval pf1_at = intinf.1
  val () = mpz_add (!p, !(intinf.2), i)
  prval () = intinf.1 := pf1_at
in
  @(pf_gc, pf_at | p)
end // end of [add_intinf_int]

implement add_intinf_intinf (intinf1, intinf2) = let
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p)
  prval pf1_at = intinf1.1
  prval pf2_at = intinf2.1
  val () = mpz_add (!p, !(intinf1.2), !(intinf2.2))
  prval () = intinf1.1 := pf1_at
  prval () = intinf2.1 := pf2_at
in
  @(pf_gc, pf_at | p)
end // end of [add_intinf_intinf]

//

implement sub_intinf_int (intinf, i) = let
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p)
  prval pf1_at = intinf.1
  val () = mpz_sub (!p, !(intinf.2), i)
  prval () = intinf.1 := pf1_at
in
  @(pf_gc, pf_at | p)
end // end of [sub_intinf_int]

implement sub_intinf_intinf (intinf1, intinf2) = let
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p)
  prval pf1_at = intinf1.1
  prval pf2_at = intinf2.1
  val () = mpz_sub (!p, !(intinf1.2), !(intinf2.2))
  prval () = intinf1.1 := pf1_at
  prval () = intinf2.1 := pf2_at
in
  @(pf_gc, pf_at | p)
end // end of [sub_intinf_intinf]

//

implement mul_intinf_int {m,n} (intinf, i) = let
  prval pf_mul = mul_make {m,n} ()
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p)
  prval pf1_at = intinf.1
  val () = mpz_mul (!p, !(intinf.2), i)
  prval () = intinf.1 := pf1_at
in
  @(pf_mul | @(pf_gc, pf_at | p))
end // end of [mul_intinf_int]

implement mul_intinf_intinf {m,n} (intinf1, intinf2) = let
  prval pf_mul = mul_make {m,n} ()
  val @(pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p)
  prval pf1_at = intinf1.1
  prval pf2_at = intinf2.1
  val () = mpz_mul (!p, !(intinf1.2), !(intinf2.2))
  prval () = intinf1.1 := pf1_at
  prval () = intinf2.1 := pf2_at
in
  @(pf_mul | @(pf_gc, pf_at | p))
end // end of [mul_intinf_intinf]

(* ****** ****** *)

(* end of [intinf.dats] *)
