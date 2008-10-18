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

// author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // loaded by [ats_main_prelude]

(* ****** ****** *)

local // for call-by-need lazy evaluation

assume lazy_t0ype_type (a:t@ype) = ref (thunkvalue a)
assume lazy_viewt0ype_viewtype (a:viewt@ype) = thunkvalue_vt a

in

implement{a} lazy_force_crypt (r) = $effmask_ref let
  val (vbox pf | p) = begin
    ref_get_view_ptr ($decrypt r) // this effect is ignored!
  end // end of [val]
in
  case+ !p of
  | ~thunkvalue_thunk (xf) => let
      val x = $effmask_ref ((xf: () -<cloref1> a) ())
    in
      !p := thunkvalue_value x; x
    end // end of [thunkvalue_thunk]
  | thunkvalue_value (x) => let val () = fold@ (!p) in x end
    // end of [thunkvalue_value]
end // end of [lazy_force_crypt]

//

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

(* ****** ****** *)

#define nil stream_nil
#define cons stream_cons
#define :: stream_cons

(* ****** ****** *)

fun{a:t@ype} stream_filter_con
  (xs: stream a, p: a -<cloptr1,~ref> bool)
  :<1,~ref> stream_con a = begin
  case+ lazy_force xs of
  | stream_cons (x, xs) => begin
      if p x then stream_cons (x, stream_filter<a> (xs, p))
      else stream_filter_con (xs, p)
    end
  | stream_nil () => begin
      cloptr_free p; stream_nil ()
    end
end // end of [stream_filter_con]

implement{a} stream_filter (xs, p) =
  $delay (stream_filter_con<a> (xs, p))

fun{a:t@ype} stream_vt_filter_con
  (xs: stream_vt a, p: a -<cloptr1,~ref> bool)
  :<1,~ref> stream_vt_con a = let
  val xs_con = lazy_vt_force xs
in
  case+ xs_con of
  | stream_vt_cons (x, !xs_ptr) => begin
      if p x then let
        val xs_val = !xs_ptr
        val () = !xs_ptr := stream_vt_filter (xs_val, p)
      in
        fold@ {a} (xs_con); xs_con
      end else let
        val xs_val = !xs_ptr
      in
        free@ {a} (xs_con); stream_vt_filter_con (xs_val, p)
      end
    end
  | stream_vt_nil () => begin
      fold@ xs_con; cloptr_free p; xs_con
    end
end // end of [stream_vt_filter_con]

implement{a} stream_vt_filter (xs, p) =
  $delay (stream_vt_filter_con<a> (xs, p))

(* ****** ****** *)

fun{a,b:t@ype} stream_map_con
  (xs: stream a, f: a -<cloptr1,~ref> b)
  :<1,~ref> stream_con b = begin
  case+ lazy_force xs of
  | x :: xs => f x :: $delay (stream_map_con (xs, f))
  | nil () => (cloptr_free f; nil ())
end // end of [stream_map_con]

implement{a,b} stream_map (xs, f) =
  $delay (stream_map_con<a,b> (xs, f))

//

fun{a1,a2,b:t@ype} stream_map2_con (
    xs1: stream a1
  , xs2: stream a2
  , f: (a1, a2) -<cloptr1,~ref> b
  ) :<1,~ref> stream_con b = begin
  case+ lazy_force xs1 of
  | x1 :: xs1 => begin case+ lazy_force xs2 of
    | x2 :: xs2 => begin
        f (x1, x2) :: $delay (stream_map2_con<a1,a2,b> (xs1, xs2, f))
      end
    | nil () => let val () = cloptr_free f in nil () end
    end
  | nil () => let val () = cloptr_free f in nil () end
end // end of [stream_map2_con]

implement{a1,a2,b} stream_map2 (xs1, xs2, f) =
  $delay (stream_map2_con<a1,a2,b> (xs1, xs2, f))

(* ****** ****** *)

fun{a:t@ype} stream_merge_ord_con (
    xs10: stream a
  , xs20: stream a
  , lte: (a, a) -<cloptr1,~ref> bool
  ) :<1,~ref> stream_con a = begin
  case+ lazy_force xs10 of
  | x1 :: xs1 => begin case+ lazy_force xs20 of
    | x2 :: xs2 => begin
        if lte (x1, x2) then begin
          x1 :: stream_merge_ord (xs1, xs20, lte)
        end else begin
          x2 :: $delay (stream_merge_ord_con (xs10, xs2, lte))
        end
      end // end of [::]
    | nil () => begin
        let val () = cloptr_free lte in x1 :: xs1 end
      end // end of [nil]
    end // end of [::]
  | nil () => begin
      let val () = cloptr_free lte in lazy_force xs20 end
    end // end of [nil]
end // end of [stream_merge_ord_con]

implement{a} stream_merge_ord (xs10, xs20, lte) =
  $delay (stream_merge_ord_con (xs10, xs20, lte))

(* ****** ****** *)

implement{a} stream_nth (xs, n) = begin
  case+ lazy_force xs of
    | x :: xs => if n = 0 then x else stream_nth<a> (xs, n-1)
    | nil () => $raise StreamSubscriptException
end // end of [stream_nth]

(* ****** ****** *)

(* end of [lazy.dats] *)
