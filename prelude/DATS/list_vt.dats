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

// some built-in static constants for linear list operations

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // loaded by [ats_main_prelude]

(* ****** ****** *)

#define nil list_vt_nil
#define cons list_vt_cons
#define :: list_vt_cons

(* ****** ****** *)

implement list_vt_length_is_nonnegative (xs) = begin
  case+ xs of list_vt_cons _ => fold@ xs | list_vt_nil () => fold@ xs
end // end of [list_vt_length_is_nonnegative]

(* ****** ****** *)

fn list_vt_is_cons {a:viewt@ype} {n:nat} (xs: !list_vt (a, n)): bool (n>0) =
  case+ xs of cons _ => (fold@ xs; true) | nil () => (fold@ xs; false)

(* ****** ****** *)

// A feature in this implementation is yet to be realized

viewtypedef List_vt = [a:viewt@ype] List_vt a

implement{a} list_vt_of_arraysize (arrsz) = let
  fun loop {n:nat} {l1,l2:addr} .<n>. (
      pf1: !array_v (a, n, l1) >> array_v (a?, n, l1)
    , pf2: !List_vt? @ l2 >> list_vt (a, n) @ l2
    | p_arr: ptr l1, res: ptr l2, n: int n
    ) :<> void =
    if n > 0 then let
      prval (pf11, pf12) = array_v_uncons {a} (pf1)
      val () = !res := cons {a} {0} (!p_arr, ?)
      val cons (_, !res_next) = !res
      val () = loop 
        (pf12, view@ (!res_next) | p_arr+sizeof<a>, res_next, n-1)
      // end of [val]
      prval () = pf1 := array_v_cons {a?} (pf11, pf12)
    in
      fold@ (!res)
    end else let
      prval () = array_v_unnil {a} (pf1)
      prval () = pf1 := array_v_nil {a?} ()        
    in
      !res := nil {a} ()
    end // end of [if]
  // end of [loop]
  var res: List_vt?
  val (pf_gc, pf_arr | p_arr, sz) = arrsz
  val () = loop (pf_arr, view@ res | p_arr, &res, sz)
in
  array_ptr_free {a} (pf_gc, pf_arr | p_arr); res
end // end of [list_vt_of_arraysize]

(*

implement{a} list_vt_of_arraysize (arrsz) = let

// the loop goes from the end of an array to its beginning
fun loop {i,j:nat} {l:addr} {ofs:int} .<i>.
  (pf_mul: MUL (i, sizeof a, ofs), pf_arr: array_v (a, i, l) |
   i: int i, p: ptr (l+ofs), res: list_vt (a, j))
  :<> (array_v (a?, i, l) | list_vt (a, i+j)) =
  if i > 0 then let
    prval pf1_mul = mul_add_const {~1} (pf_mul)
    prval (pf1_arr, pf_lst) = array_v_unextend {a} (pf_mul, pf_arr)
    val p1 = p - sizeof<a>
    val x = ptr_get_vt (pf_lst | p1)
    val (pf1_arr | res) = loop (pf1_mul, pf1_arr | i-1, p1, cons (x, res))
    prval pf_arr = array_v_extend (pf1_mul, pf1_arr, pf_lst)
  in
    (pf_arr | res)    
  end else let
    prval () = array_v_unnone {a} (pf_arr)
  in
    (array_v_none {a?} () | res)
  end

val (pf_arr | p_arr, sz) = arrsz
val (pf_mul | ofs) = sz imul2 sizeof<a>
val (pf_arr | res) = loop (pf_mul, pf_arr | sz, p_arr+ofs, nil ())

in
  array_ptr_free {a} (pf_arr | p_arr); res
end // end of [list_vt_of_arraysize]

*)

(* ****** ****** *)

implement{a} list_vt_copy (xs0) = let
  fun loop {n:nat} .<n>.
    (xs: !list_vt (a, n), res: &List_vt a? >> list_vt (a, n))
    :<> void = case+ xs of
    | cons (x, !p_xs1) => let
        val () = res := cons {a} {0} (x, ?)
        val+ cons (_, !p_res1) = res; val () = loop (!p_xs1, !p_res1)
      in
        fold@ xs; fold@ res
      end // end of [cons]
    | nil () => (fold@ xs; res := nil ())
  var res: List_vt a // uninitialized
in
  loop (xs0, res); res
end // end of [list_vt_copy]

(* ****** ****** *)

implement{a} list_vt_free (xs0) = let
  fun loop {n:nat} .<n>. (xs: list_vt (a, n)):<> void =
    case+ xs of ~cons (_, xs) => loop xs | ~nil () => ()
in
  loop (xs0)
end // end of [list_vt_free]

(* ****** ****** *)

implement{a} list_vt_length (xs0) = loop (xs0, 0) where {
  fun loop {i,j:nat} .<i>.
    (xs: !list_vt (a, i), j: int j):<> int (i+j) = begin
    case+ xs of
    | cons (_, !xs1) =>
        let val n = loop (!xs1, j+1) in fold@ xs; n end
    | nil () => (fold@ xs; j)
  end // end of [loop]
} // end of [list_vt_length]

(* ****** ****** *)

implement{a} list_vt_append (xs0, ys0) = let
  var xs0 = xs0
  fun{a:viewt@ype} loop {m,n:nat} .<m>.
    (xs0: &list_vt (a, m) >> list_vt (a, m+n), ys0: list_vt (a, n))
    :<> void = begin case+ xs0 of
    | cons (_, !xs) => (loop (!xs, ys0); fold@ xs0) | ~nil () => (xs0 := ys0)
  end // end of [loop]
in
  loop (xs0, ys0); xs0
end // end of [list_vt_append]

(* ****** ****** *)

implement{a} list_vt_reverse (xs0) = let

fun revapp {m,n:nat} .<m>.
  (xs: list_vt (a, m), ys: list_vt (a, n)):<> list_vt (a, m+n) =
  case+ xs of
  | cons (!x, !xs1) => let
      val xs1_v = !xs1
    in
      !xs1 := ys; fold@ xs; revapp (xs1_v, xs)
    end
  | ~nil () => ys

in
  revapp (xs0, nil ())
end // end of [list_vt_reverse]

(* ****** ****** *)

implement{a} list_vt_foreach_main
  {v} {vt} {n} {f} (pf | xs0, f, env) = let
  viewtypedef fun_t = (!v | &a, !vt) -<f> void
  fun loop {i:nat} .<i>.
    (pf: !v | xs0: !list_vt (a, i), f: !fun_t, env: !vt):<f> void =
    case+ xs0 of
    | cons (!x, !xs) => begin
        f (pf | !x, env); loop (pf | !xs, f, env); fold@ xs0
      end
    | nil () => (fold@ xs0)
in
  loop (pf | xs0, f, env)
end

(* ****** ****** *)

// [list_vt.sats] is already loaded by a call to [pervasive_load]
staload _(*anonymous*) = "prelude/SATS/list_vt.sats" // this forces that the static
// loading function for [list_vt.sats] is to be called at run-time
// this is really needed only if some datatypes are declared in [list_vt.sats]

(* ****** ****** *)

(* end of [list_vt.dats] *)
