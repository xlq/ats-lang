(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2012 Hongwei Xi, Boston University
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

staload
UN = "prelude/SATS/unsafe.sats"
staload "prelude/SATS/dlist_vt.sats"

(* ****** ****** *)

sortdef t0p = t@ype
sortdef vt0p = viewt@ype

(* ****** ****** *)

dataviewtype
DLIST (a:viewt@ype+, int) =
  | {r:nat}
    DLISTcons (a, r+1) of (a, ptr(*prev*), DLIST (a, r))
  | DLISTnil (a, 0) of ()
// end of [DLIST]

extern
castfn dlist2ptr {a:vt0p}{r:int} (xs: !DLIST(a, r)):<> ptr

(* ****** ****** *)

assume
dlist_viewt0ype_int_int_viewtype
  (a: vt0p, f:int, r:int) = DLIST (a, r)
// end of [assume]

(* ****** ****** *)

implement{a} dlist_vt_nil () = DLISTnil ()

(* ****** ****** *)

implement{a}
dlist_vt_cons (x, xs) =
  case+ xs of
  | DLISTcons
      (_, !p_prev, _) => let
      prval () = fold@ (xs)
      val res = DLISTcons (x, null, xs)
      val () = $UN.ptrset<ptr> (p_prev, dlist2ptr(res))
    in
      res
    end // end of [DLISTcons]
  | ~DLISTnil () => DLISTcons (x, null, DLISTnil ())
// end of [dlist_vt_cons]

(* ****** ****** *)

implement{a}
dlist_vt_snoc (xs, x) = let
  val node =
    DLISTcons (x, dlist2ptr(xs), DLISTnil ())
  val node1 = __copy (node) where {
    extern castfn __copy (xs: !DLIST(a, 1)):<> DLIST(a, 1)
  }
  val+ DLISTcons (_, prev, !p_xs) = xs
  val+ DLISTnil () = !p_xs; val () = !p_xs := node1
  prval () = fold@ {a} (xs)
  prval () = __hide (xs) where {
    extern praxi __hide (xs: DLIST(a, 2)):<> void
  } // end of [prval]
in
  node
end // end of [dlist_vt_snoc]

(* ****** ****** *)

implement{a}
dlist_vt_length_f
  {f,r} (xs) = let
//
  fun loop {f:nat} .<f>.
    (prev: ptr, res: int):<> int = let
    val xs = __cast (prev) where {
      extern castfn __cast (p: ptr):<> [r:nat] DLIST (a, r)
    } // end of [val]
  in
    case+ xs of
    | DLISTcons
        (_, prev, _) => let
        prval () = fold@ {a} (xs)
        prval () = __assert () where {
          extern praxi __assert (): [f > 0] void
        } // end of [prval]
        prval () = __free (xs) where {
          extern praxi __free {r:int} (xs: DLIST (a, r)): void
        } // end of [prval]
      in
        loop {f-1} (prev, res + 1)
      end // end of [DLISTcons]
    | ~DLISTnil () => res
  end // end of [loop]
//
  prval () = lemma1_dlist_vt_params {a}{f,r} (xs)
//
  val res = (
    case+ xs of
    | DLISTcons (_, prev, _) => let
        prval () = fold@ (xs) in loop {f} (prev, 0)
      end // end of [DLISTcons]
    | DLISTnil () => (fold@ (xs); 0)
  ) : int // end of [val]
in
  __cast (res) where {
    extern praxi __cast (res: int): int (f)
  } // end of [__cast]
end // end of [dlist_vt_length_f]

(* ****** ****** *)

implement{a}
dlist_vt_length_r
  {f,r} (xs) = let
  fun loop {r:nat}{r0:int} .<r>.
    (xs: !DLIST (a, r), res: int (r0)):<> int (r0+r) =
    case+ xs of
    | DLISTcons (_, _, !p_xs) => let
        val res = loop (!p_xs, res + 1); prval () = fold@ (xs)
      in
        res
      end // end of [DLISTcons]
    | DLISTnil () => (fold@ (xs); res)
  // end of [loop]
  prval () = lemma1_dlist_vt_params {a}{f,r} (xs)
in
  loop (xs, 0)
end // end of [dlist_vt_length_r]

(* ****** ****** *)

(* end of [dlist_vt.dats] *)
