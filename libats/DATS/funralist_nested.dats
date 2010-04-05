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
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
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

(*
**
** A functional random-access list implementation based on nested datatypes
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: April, 2010 // based on a version done in DML (circa. 2000)
**
*)

(* ****** ****** *)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no static loading at run-time

(* ****** ****** *)

staload "libats/SATS/funralist_nested.sats"

(* ****** ****** *)

typedef P (a1:t@ype) (a2:t@ype) = '(a1, a2)

datatype ralist (a:t@ype+, int) =
  | {n:pos} RAevn (a, n+n) of ralist (P a a, n)
  | {n:nat} RAodd (a, n+n+1) of (a, ralist (P a a, n))
  | RAnil (a, 0)
// end of [ralist]

(* ****** ****** *)

macdef P x0 x1 = '( ,(x0), ,(x1) )

(* ****** ****** *)

assume list_t0ype_type (a:t@ype, n:int) = ralist (a, n)

(* ****** ****** *)

implement{} funralist_make_nil {elt} () = RAnil ()

(* ****** ****** *)

implement{elt}
funralist_length (xs) = length<elt> (xs) where {
  fun{elt:t@ype}
  length {n:nat} .<n>.
    (xs: ralist (elt, n)):<> int n = let
    typedef elt2 = P elt elt
  in
    case+ xs of
    | RAevn xxs => 2 * length<elt2> (xxs)
    | RAodd (_, xxs) => 2 * length<elt2> (xxs) + 1
    | RAnil () => 0
  end // end of [length]
} // end of [funralist_length]

(* ****** ****** *)

implement{elt}
funralist_cons (x0, xs) = cons<elt> (x0, xs) where {
  fun{elt:t@ype} cons {n:nat} .<n>.
    (x0: elt, xs: ralist (elt, n)):<> ralist (elt, n+1) = let
    typedef elt2 = P elt elt
  in
    case+ xs of
    | RAevn xxs => RAodd (x0, xxs)
    | RAodd (x, xxs) => RAevn (cons<elt2> (P x0 x, xxs))
    | RAnil _ => RAodd (x0, RAnil ())
  end // end of [cons]
} // end of [ralist_cons]

(* ****** ****** *)

implement{elt}
funralist_uncons
  (xs, x0) = uncons<elt> (xs, x0) where {
  fun{elt:t@ype} uncons {n:pos} .<n>.
    (xs: ralist (elt, n), x0: &elt? >> elt)
    :<> ralist (elt, n-1) = let
    typedef elt2 = P elt elt
  in
    case+ xs of
    | RAevn xxs => let
        var xx0: elt2 // uninitialized
        val xxs = uncons<elt2> (xxs, xx0); val () = x0 := xx0.0
      in
        RAodd {elt} (xx0.1, xxs)
      end // end of [RAevn]
    | RAodd (x, xxs) => let
        val () = x0 := x in
        case+ xxs of RAnil _ => RAnil () | _ =>> RAevn xxs
      end // end of [RAodd]
  end // end of [uncons]
} // end of [funralist_uncons]

(* ****** ****** *)

implement{elt}
funralist_lookup
  (xs, i) = lookup<elt> (xs, i) where {
  fun{elt:t@ype}
  lookup {n,i:nat | i < n} .<n>.
    (xs: ralist (elt, n), i: int i):<> elt = let
    typedef elt2 = P elt elt
  in
    case+ xs of
    | RAodd (x, xxs) => begin
        if i = 0 then x else let
          val x01 = lookup<elt2> (xxs, nhalf (i-1))
        in
          if i nmod 2 = 0 then x01.1 else x01.0
        end // end of [if]
      end // end of [RAodd]
    | RAevn xxs => let
        val x01 = lookup<elt2> (xxs, nhalf i)
      in
        if i nmod 2 = 0 then x01.0 else x01.1
      end // end of [RAevn]
  end // end of [lookup]
} // end of [funralist_lookup]

(* ****** ****** *)

//
// Here is an example of constructing linear closures explicitly
//

dataviewtype closure_ (a:t@ype) =
  {param: viewtype} CLOSURE_ (a) of (param, (param, a) -<fun> a)
// end of [closure_]

fn{a:t@ype}
cloapp (c: closure_ a, x: a):<> a = let
  val+ ~CLOSURE_ {..} {param} (p, f) = c; val f = f: (param, a) -<fun> a
in
  f (p, x)
end // end of [cloapp]
  
fun{a:t@ype}
fupdate {n,i:nat | i < n} .<n>.
  (xs: ralist (a, n), i: int i, c: closure_ a):<> ralist (a, n) = let
  fn f0 (c: closure_ a, xx: P a a):<> P a a = '(cloapp<a> (c, xx.0), xx.1)
  fn f1 (c: closure_ a, xx: P a a):<> P a a = '(xx.0, cloapp<a> (c, xx.1))
in
  case+ xs of
  | RAodd (x, xxs) => begin
      if i = 0 then RAodd (cloapp<a> (c, x), xxs) else let
        val i1 = i - 1; val i2 = i1 / 2; val parity = i1 - (i2 + i2)
      in
        if parity = 0 then begin
          RAodd (x, fupdate<P a a> (xxs, i2, CLOSURE_ {P a a} (c, f0)))
        end else begin
          RAodd (x, fupdate<P a a> (xxs, i2, CLOSURE_ {P a a} (c, f1)))
        end // end of [if]
      end // end of [if]
    end // end of [RAodd]
  | RAevn xxs => let
      val i2 = i / 2; val parity = i - (i2 + i2)
    in
      if parity = 0 then begin
        RAevn (fupdate<P a a> (xxs, i2, CLOSURE_ {P a a} (c, f0)))
      end else begin
        RAevn (fupdate<P a a> (xxs, i2, CLOSURE_ {P a a} (c, f1)))
      end // end of [if]
    end // end of [RAevn]
end // end of [fupdate]

implement{elt}
funralist_update (xs, i, x) = let
  val f0 = lam (x_box: box_vt elt, _: elt): elt =<fun> let val+ ~box_vt (x) = x_box in x end
in
  fupdate<elt> (xs, i, CLOSURE_ (box_vt x, f0))
end // end of [funralist_update]

(* ****** ****** *)

(* end of [funralist_nested.dats] *)
