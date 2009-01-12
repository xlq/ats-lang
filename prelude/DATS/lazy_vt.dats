(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

// author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // loaded by [ats_main_prelude]

(* ****** ****** *)

(*

local // for call-by-need lazy evaluation

assume lazy_viewt0ype_viewtype (a:viewt@ype) = thunkvalue_vt a

in

implement{a} lazy_vt_force_crypt (v_lazy) = begin
  case+ $decrypt (v_lazy) of
  | ~thunkvalue_vt_thunk (xf) => let
      stavar T: t@ype
      val x = $effmask_ref((xf: () -<lin,cloptr1> a) ())
      val (pf_gc, pf_at | p) = cloptr_get_view_ptr {T} (xf)
    in
      ptr_free (pf_gc, pf_at | p); x
    end // end of [thunkvalue_vt_thunk]
  | ~thunkvalue_vt_value (x) => x
end // end of [lazy_vt_force_crypt]

end // end of [local]

*)

(* ****** ****** *)

#define nil stream_vt_nil
#define cons stream_vt_cons
#define :: stream_vt_cons

(* ****** ****** *)

fun{a:t@ype} stream_vt_filter_cloptr_con
  (xs: stream_vt a, p: a -<cloptr1,~ref> bool)
  :<1,~ref> stream_vt_con a = let
  val xs_con = !xs
in
  case+ xs_con of
  | stream_vt_cons (x, !xs_ptr) => begin
      if p x then let
        val xs_val = !xs_ptr
        val () = !xs_ptr := stream_vt_filter_cloptr (xs_val, p)
      in
        fold@ {a} (xs_con); xs_con
      end else let
        val xs_val = !xs_ptr
        val () = free@ {a} (xs_con)
      in
        stream_vt_filter_cloptr_con (xs_val, p)
      end // end of [if]
    end // end of [stream_vt_cons]
  | stream_vt_nil () => begin
      fold@ xs_con; cloptr_free p; xs_con
    end // end of [stream_vt_nil]
end // end of [stream_vt_filter_con]

implement{a} stream_vt_filter_fun (xs, p) =
  $delay_vt (stream_vt_filter_cloptr_con<a> (xs, lam x => p x), ~xs)

implement{a} stream_vt_filter_cloptr (xs, p) =
  $delay_vt (stream_vt_filter_cloptr_con<a> (xs, p), (cloptr_free p; ~xs))

(* ****** ****** *)

fun{a1,a2,b:t@ype} stream_vt_map2_cloptr_con (
    xs1: stream_vt a1
  , xs2: stream_vt a2
  , f: (a1, a2) -<cloptr1,~ref> b
  ) :<1,~ref> stream_vt_con b = begin case+ !xs1 of
  | ~(x1 :: xs1) => begin case+ !xs2 of
    | ~(x2 :: xs2) => y :: ys where {
        val y = f (x1, x2)
        val ys = $delay_vt (
          stream_vt_map2_cloptr_con<a1,a2,b> (xs1, xs2, f)
        , (~xs1; ~xs2; cloptr_free f)
        ) // end of [val ys]
      } // end of [::]
    | ~nil () => (~xs1; cloptr_free f; nil ())
    end // end of [::]
  | ~nil () => (~xs2; cloptr_free f; nil ())
end // end of [stream_map2_con]

implement{a1,a2,b} stream_vt_map2_fun (xs1, xs2, f) = $delay_vt (
  stream_vt_map2_cloptr_con<a1,a2,b> (xs1, xs2, lam (x1, x2) => f (x1, x2))
, (~xs1; ~xs2)
) // end of [stream_map2_fun]

implement{a1,a2,b} stream_vt_map2_cloptr (xs1, xs2, f) = $delay_vt (
  stream_vt_map2_cloptr_con<a1,a2,b> (xs1, xs2, f)
, (~xs1; ~xs2; cloptr_free f)
)

(* ****** ****** *)

(* end of [lazy_vt.dats] *)
