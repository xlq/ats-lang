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
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

(*
#define ATS_STALOADFLAG 0 // ...
*)
#define ATS_DYNLOADFLAG 0 // loaded by [ats_main_prelude]

(* ****** ****** *)

// list implementation

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)
//
// this is a proof function
//
implement
list_length_is_nonnegative (xs) =
  case+ xs of list_cons _ => () | list_nil () => ()
// end of [list_length_is_nonnegative]

(* ****** ****** *)

// this is a casting function
implement
list_of_list_vt {a} (xs) = aux (xs) where {
  castfn aux {n:nat} .<n>.
    (xs: list_vt (a, n)):<> list (a, n) =
    case+ xs of
    | ~list_vt_cons (x, xs) => list_cons (x, aux xs)
    | ~list_vt_nil () => list_nil ()
  // end of [aux]
} // end of [list_of_list_vt]

(* ****** ****** *)

implement{a}
list_app__main
  {v} {vt} {f:eff} (pf | xs, f, env) = let
  typedef fun_t = (!v | a, !vt) -<fun,f> void
  fun loop {n:nat} .<n>. (
      pf: !v
    | xs: list (a, n)
    , f: fun_t
    , env: !vt
    ) :<f> void = begin case+ xs of
    | x :: xs => let
        val () = f (pf | x, env) in loop (pf | xs, f, env)
      end // end of [::]
    | nil () => ()
  end // end of [loop]
in
  loop (pf | xs, f, env)
end // end of [list_app__main]

implement{a}
list_app_fun {f:eff} (xs, f) = let
  val f = coerce (f) where {
    extern castfn coerce (f: a -<f> void):<> (!unit_v | a, !ptr) -<f> void
  } // end of [where]
  prval pf = unit_v ()
  val () = list_app__main<a> {..} {ptr} (pf | xs, f, null)
  prval unit_v () = pf
in
  ()
end // end of [list_app_fun]

implement{a}
list_app_clo {v} {f:eff} (pf1 | xs, f) = let
  viewtypedef clo_t = (!v | a) -<clo,f> void
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  prval pf = (pf1, view@ f)
  fn app (pf: !V | x: a, p_f: !ptr l_f):<f> void = let
    prval (pf1, pf2) = pf
    val () = !p_f (pf1 | x)
    prval () = pf := (pf1, pf2)
  in
    // nothing
  end // end of [app]
  val () = list_app__main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = pf1 := pf.0
  prval () = view@ f := pf.1
in
  ()
end // end of [list_app_clo]

implement{a}
list_app_cloptr
  {v:view} {f:eff} (pf | xs, f) = let
  viewtypedef cloptr_t = (!v | a) -<cloptr,f> void
  fn app (pf: !v | x: a, f: !cloptr_t):<f> void = f (pf | x)
in
  list_app__main<a> {v} {cloptr_t} (pf | xs, app, f)
end // end of [list_app_cloptr]

implement{a}
list_app_cloref {f:eff} (xs, f) = let
  typedef cloref_t = a -<cloref,f> void
  fn app (pf: !unit_v | x: a, f: !cloref_t):<f> void = f (x)
  prval pf = unit_v ()
  val () = list_app__main<a> {unit_v} {cloref_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  ()
end // end of [list_app_cloref]

(* ****** ****** *)

implement{a1,a2}
list_app2__main
  {v:view} {vt:viewtype}
  {n} {f:eff} (pf | xs1, xs2, f, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | xs1: list (a1, n)
    , xs2: list (a2, n)
    , f: (!v | a1, a2, !vt) -<fun,f> void
    , env: !vt
  ) :<f> void = case+ (xs1, xs2) of
    | (x1 :: xs1, x2 :: xs2) => begin
        f (pf | x1, x2, env); loop (pf | xs1, xs2, f, env)
      end // end of [::, ::]
    | (nil (), nil ()) => ()
  // end of [loop]
in
  loop (pf | xs1, xs2, f, env)
end // end of [list_app2__main]

implement{a1,a2}
list_app2_fun {n} {f:eff} (xs1, xs2, f) = let
  val f = coerce (f) where { extern castfn
    coerce (f: (a1, a2) -<f> void):<> (!unit_v | a1, a2, !ptr) -<f> void
  } // end of [where]
  prval pf = unit_v ()
  val () = list_app2__main<a1,a2> {..} {ptr} (pf | xs1, xs2, f, null)
  prval unit_v () = pf
in
  // empty
end // end of [list_app2_fun]

implement{a1,a2}
list_app2_clo
  {v} {n} {f:eff} (pf1 | xs1, xs2, f) = let
  typedef clo_t = (!v | a1, a2) -<clo,f> void
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | x1: a1, x2: a2, p_f: !ptr l_f):<f> void = let
    prval (pf1, pf2) = pf
    val () = !p_f (pf1 | x1, x2)
    prval () = pf := (pf1, pf2)
  in
    // nothing
  end // end of [app]
  prval pf = (pf1, view@ f)
  val () = list_app2__main<a1,a2> {V} {ptr l_f} (pf | xs1, xs2, app, p_f)
  prval () = pf1 := pf.0
  prval () = view@ f := pf.1
in
  // empty
end // end of [list_app2_clo]

implement{a1,a2}
list_app2_cloptr
  {v} {n} {f:eff} (pf | xs1, xs2, f) = let
  viewtypedef cloptr_t = (!v | a1, a2) -<cloptr,f> void
  fn app (pf: !v | x1: a1, x2: a2, f: !cloptr_t):<f> void = f (pf | x1, x2)
  val () = begin
    list_app2__main<a1,a2> {v} {cloptr_t} (pf | xs1, xs2, app, f)
  end // end of [val]
in
  // empty
end  // end of [list_app2_cloptr]

implement{a1,a2}
list_app2_cloref {n} {f:eff} (xs1, xs2, f) = let
  typedef cloref_t = (a1, a2) -<cloref,f> void
  fn app (pf: !unit_v | x1: a1, x2: a2, f: !cloref_t):<f> void = f (x1, x2)
  prval pf = unit_v ()
  val () = begin
    list_app2__main<a1,a2> {unit_v} {cloref_t} (pf | xs1, xs2, app, f)
  end // end of [val]
  prval unit_v () = pf
in
  // empty
end  // end of [list_app2_cloref]

(* ****** ****** *)

// a tail-recursive implementation of list-append

implement{a}
list_append {i,j} (xs, ys) = let
  var res: List a // uninitialized
  fun loop {n1,n2:nat} .<n1>.
    (xs: list (a, n1), ys: list (a, n2), res: &(List a)? >> list (a, n1+n2))
    :<> void = begin case+ xs of
    | x :: xs => let
        val () = (res := cons {a} {0} (x, ?)); val+ cons (_, !p) = res
      in
        loop (xs, ys, !p); fold@ res
      end
    | nil () => (res := ys)
  end // end of [loop]
in
  loop (xs, ys, res); res
end // end of [list_append]

(*
//
// standard non-tail-recursive implementation of list-append
//
implement{a}
list_append {i,j} (xs, ys) = let
  fun aux {n1,n2:nat} .<n1>.
    (xs: list (a, n1), ys: list (a, n2)):<> list (a, n1+n2) =
    case+ xs of x :: xs => x :: aux (xs, ys) | nil () => ys
in
  aux (xs, ys)
end // end of [list_append]
*)

implement{a}
list_append_vt {i,j} (xs, ys) = let
  var res: List_vt a // uninitialized
  fun loop {n1,n2:nat} .<n1>.
    (xs: list (a, n1), ys: list_vt (a, n2), res: &(List_vt a)? >> list_vt (a, n1+n2))
    :<> void = begin case+ xs of
    | x :: xs => let
        val () = (res := list_vt_cons {a} {0} (x, ?)); val+ list_vt_cons (_, !p) = res
      in
        loop (xs, ys, !p); fold@ res
      end
    | nil () => (res := ys)
  end // end of [loop]
in
  loop (xs, ys, res); res
end // end of [list_append_vt]

(* ****** ****** *)

implement{a1,a2}
list_assoc__main
  {v} {vt} {eq:eff} (pf | xys, eq, x0, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | xys: list (@(a1, a2), n)
    , eq: (!v | a1, a1, !vt) -<fun,eq> bool
    , x0: a1
    , env: !vt
    ) :<eq> Option_vt a2 =
    case+ xys of
    | xy :: xys => begin
         if eq (pf | x0, xy.0, env) then Some_vt (xy.1) else loop (pf | xys, eq, x0, env)
      end // end of [::]
    | nil () => None_vt ()
in
  loop (pf | xys, eq, x0, env)
end // end of [list_assoc__main]

implement{a1,a2}
list_assoc_fun
  {eq:eff} (xys, eq, x0) = let
  val eq = coerce (eq) where { extern castfn
    coerce (eq: (a1, a1) -<eq> bool):<> (!unit_v | a1, a1, !ptr) -<eq> bool
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_assoc__main<a1,a2> {..} {ptr} (pf | xys, eq, x0, null)
  prval unit_v () = pf
in
  ans
end // end of [list_assoc_fun]

implement{a1,a2}
list_assoc_clo
  {v:view} {eq:eff} (pf1 | xys, eq, x0) = let
  typedef clo_t = (!v | a1, a1) -<clo,eq> bool
  stavar l_eq: addr; val p_eq: ptr l_eq = &eq
  viewdef V = (v, clo_t @ l_eq)
  fn app (pf: !V | x: a1, y: a1, p_eq: !ptr l_eq):<eq> bool = let
    prval (pf1, pf2) = pf
    val ans = !p_eq (pf1 | x, y)
    prval () = pf := (pf1, pf2)
  in
    ans
  end // end of [app]
  prval pf = (pf1, view@ eq)
  val ans = list_assoc__main<a1,a2> {V} {ptr l_eq} (pf | xys, app, x0, p_eq)
  prval () = pf1 := pf.0
  prval () = view@ eq := pf.1
in
  ans
end // end of [list_assoc_clo]

implement{a1,a2}
list_assoc_cloptr
  {v} {eq:eff} (pf | xys, eq, x0) = let
  viewtypedef cloptr_t = (!v | a1, a1) -<cloptr,eq> bool
  fn app (pf: !v | x: a1, y: a1, eq: !cloptr_t):<eq> bool = eq (pf | x, y)
  val ans = list_assoc__main<a1,a2> {v} {cloptr_t} (pf | xys, app, x0, eq)
in
  ans
end // end of [list_assoc_cloptr]

implement{a1,a2}
list_assoc_cloref
  {eq:eff} (xys, eq, x0) = let
  typedef cloref_t = (a1, a1) -<cloref,eq> bool
  fn app (pf: !unit_v | x: a1, y: a1, eq: !cloref_t):<eq> bool = eq (x, y)
  prval pf = unit_v ()
  val ans = list_assoc__main<a1,a2> {unit_v} {cloref_t} (pf | xys, app, x0, eq)
  prval unit_v () = pf
in
  ans
end // end of [list_assoc_cloref]

(* ****** ****** *)

implement{a}
list_concat (xss) = let
  fun aux {n:nat} .<n>.
    (xs0: List a, xss: list (List a, n)):<> List a =
    case+ xss of
    | xs :: xss => list_append (xs0, aux (xs, xss))
    | nil () => xs0
in
  case+ xss of xs :: xss => aux (xs, xss) | nil () => nil ()
end // end of [list_concat]

(* ****** ****** *)

implement{a}
list_drop (xs, i) = loop (xs, i) where {
  fun loop {n,i:nat | i <= n} .<i>.
    (xs: list (a, n), i: int i):<> list (a, n-i) =
    if i > 0 then let val+ _ :: xs = xs in loop (xs, i-1) end
    else xs
} // end of [list_drop]

implement{a}
list_drop_exn (xs, i) = loop (xs, i) where {
  fun loop {n,i:nat} .<i>.
    (xs: list (a, n), i: int i):<> [i <= n] list (a, n-i) =
    if i > 0 then begin case+ xs of
      | list_cons (_, xs) => loop (xs, i-1)
      | list_nil () => $raise ListSubscriptException ()
    end else xs
} // end of [list_drop_exn]

(* ****** ****** *)

implement{a}
list_exists__main
  {v} {vt} {p:eff} (pf | xs, p, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | xs: list (a, n)
    , p: (!v | a, !vt) -<fun,p> bool
    , env: !vt
    ) :<p> bool = case+ xs of
    | x :: xs => if p (pf | x, env) then true else loop (pf | xs, p, env)
    | nil () => false
  // end of [loop]
in
  loop (pf | xs, p, env)
end // end of [list_exists__main]

implement{a}
list_exists_fun {p:eff} (xs, p) = let
  val p = coerce (p) where {
    extern castfn coerce (p: a -<p> bool):<> (!unit_v | a, !ptr) -<p> bool
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_exists__main<a> {..} {ptr} (pf | xs, p, null)
  prval unit_v () = pf
in
  ans
end // end of [list_exists_fun]

implement{a}
list_exists_clo
  {v} {p:eff} (pf1 | xs, f) = let
  typedef clo_t = (!v | a) -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | x: a, p_f: !ptr l_f):<p> bool = let
    prval (pf1, pf2) = pf
    val ans = !p_f (pf1 | x)
    prval () = pf := (pf1, pf2)
  in
    ans
  end // end of [app]
  prval pf = (pf1, view@ f)
  val ans = list_exists__main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = pf1 := pf.0
  prval () = view@ f := pf.1
in
  ans
end // end of [list_exists_clo]

implement{a}
list_exists_cloptr
  {v} {p:eff} (pf | xs, p) = let
  viewtypedef cloptr_t = (!v | a) -<cloptr,p> bool
  fn app (pf: !v | x: a, p: !cloptr_t):<p> bool = p (pf | x)
  val ans = list_exists__main<a> {v} {cloptr_t} (pf | xs, app, p)
in
  ans
end // end of [list_exists_cloptr]

implement{a}
list_exists_cloref {p:eff} (xs, p) = let
  typedef cloref_t = a -<cloref,p> bool
  fn app (pf: !unit_v | x: a, p: !cloref_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_exists__main<a> {unit_v} {cloref_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_exists_cloref]

(* ****** ****** *)

implement{a1,a2}
list_exists2__main
  {v} {vt} {n} {p:eff} (pf | xs1, xs2, p, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | xs1: list (a1, n)
    , xs2: list (a2, n)
    , p: (!v | a1, a2, !vt) -<fun,p> bool
    , env: !vt
    ) :<p> bool = begin case+ xs1 of
    | x1 :: xs1 => let
        val+ x2 :: xs2 = xs2 in
        if p (pf | x1, x2, env) then true else loop (pf | xs1, xs2, p, env)
      end (* end of [::] *)
    | nil () => false
  end // end of [loop]
in
  loop (pf | xs1, xs2, p, env)
end // end of [list_exists2__main]

implement{a1,a2}
list_exists2_fun {n} {p:eff} (xs1, xs2, p) = let
  val p = coerce (p) where { extern castfn
    coerce (p: (a1, a2) -<p> bool):<> (!unit_v | a1, a2, !ptr) -<p> bool
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_exists2__main<a1,a2> {..} {ptr} (pf | xs1, xs2, p, null)
  prval unit_v () = pf
in
  ans
end // end of [list_exists2_fun]

implement{a1,a2}
list_exists2_clo
  {v} {n} {p:eff} (pf1 | xs1, xs2, f) = let
  typedef clo_t = (!v | a1, a2) -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | x1: a1, x2: a2, p_f: !ptr l_f):<p> bool = let
    prval (pf1, pf2) = pf
    val ans = !p_f (pf1 | x1, x2)
    prval () = pf := (pf1, pf2)
  in
    ans
  end // end of [app]
  prval pf = (pf1, view@ f)
  val ans = list_exists2__main<a1,a2> {V} {ptr l_f} (pf | xs1, xs2, app, p_f)
  prval () = pf1 := pf.0
  prval () = view@ f := pf.1
in
  ans
end // end of [list_exists2_clo]

implement{a1,a2}
list_exists2_cloptr
  {v} {n} {p:eff} (pf | xs1, xs2, p) = let
  viewtypedef cloptr_t = (!v | a1, a2) -<cloptr,p> bool
  fn app (pf: !v | x1: a1, x2: a2, p: !cloptr_t):<p> bool = p (pf | x1, x2)
  val ans = list_exists2__main<a1,a2> {v} {cloptr_t} (pf | xs1, xs2, app, p)
in
  ans
end // end of [list_exists2_cloptr]

implement{a1,a2}
list_exists2_cloref {n} {p:eff} (xs1, xs2, p) = let
  viewtypedef cloref_t = (a1, a2) -<cloref,p> bool
  fn app (pf: !unit_v | x1: a1, x2: a2, p: !cloref_t):<p> bool = p (x1, x2)
  prval pf = unit_v ()
  val ans = list_exists2__main<a1,a2> {unit_v} {cloref_t} (pf | xs1, xs2, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_exists2_cloref]

(* ****** ****** *)

implement{a}
list_extend (xs, y) = let
  var res: List_vt a // uninitialized
  fun loop {n:nat} .<n>. (
      xs: list (a, n), y: a
    , res: &(List_vt a)? >> list_vt (a, n+1)
    ) :<> void = begin
    case+ xs of
    | x :: xs => let
        val () = (res := list_vt_cons {a} {0} (x, ?)); val list_vt_cons (_, !p) = res
      in
        loop (xs, y, !p); fold@ res
      end // end of [::]
    | nil () => (res := list_vt_cons (y, list_vt_nil ()))
  end // end of [loop]
in
  loop (xs, y, res); res
end // end of [list_extend]

(* ****** ****** *)

implement{a}
list_filter__main
  {v} {vt} {n} {p:eff} (pf | xs, p, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | xs: list (a, n)
    , p: (!v | a, !vt) -<fun,p> bool
    , res: &(List_vt a)? >> list_vt (a, n1)
    , env: !vt
    ) :<p> #[n1:nat | n1 <= n] void = case+ xs of
    | x :: xs => begin
        if p (pf | x, env) then let
          val () = res := list_vt_cons {a} {0} (x, ?)
          val+ list_vt_cons (_, !p_res) = res
        in
          loop (pf | xs, p, !p_res, env); fold@ res
        end else begin
          loop (pf | xs, p, res, env)
        end // end of [if]
      end (* end of [::] *)
    | nil () => (res := list_vt_nil ())
  // end of [loop]
  var res: List_vt a // uninitialized
  val () = loop (pf | xs, p, res, env)
in
  res
end // end of [list_filter__main]

implement{a}
list_filter_fun {n} {p:eff} (xs, f) = let
  val f = coerce (f) where { extern castfn
    coerce (f: a -<p> bool):<> (!unit_v | a, !ptr) -<p> bool
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_filter__main<a> {..} {ptr} (pf | xs, f, null)
  prval unit_v () = pf
in
  ans
end // end of [list_filter_fun]

implement{a}
list_filter_clo
  {v} {n} {p:eff} (pf1 | xs, f) = let
  typedef clo_t = (!v | a) -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | x: a, p_f: !ptr l_f):<p> bool = let
    prval (pf1, pf2) = pf; val ans = !p_f (pf1 | x); prval () = pf := (pf1, pf2)
  in
    ans
  end // end of [app]
  prval pf = (pf1, view@ f)
  val ans = list_filter__main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = pf1 := pf.0
  prval () = view@ f := pf.1
in
  ans
end // end of [list_filter_clo]

implement{a}
list_filter_cloptr
  {v} {n} {p:eff} (pf | xs, p) = let
  viewtypedef cloptr_t = (!v | a) -<cloptr,p> bool
  fn app (pf: !v | x: a, p: !cloptr_t):<p> bool = p (pf | x)
  val ans = list_filter__main<a> {v} {cloptr_t} (pf | xs, app, p)
in
  ans
end // end of [list_filter_cloptr]

implement{a}
list_filter_cloref {n} {p:eff} (xs, p) = let
  typedef cloref_t = a -<cloref,p> bool
  fn app (pf: !unit_v | x: a, p: !cloref_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_filter__main<a> {unit_v} {cloref_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_filter_cloref]

(* ****** ****** *)

implement{a}
list_find__main {v} {vt} {p:eff} (pf | xs, p, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | xs: list (a, n), p: !(!v | a, !vt) -<fun,p> bool, env: !vt
    ) :<p> Option_vt a =
    case+ xs of
    | x :: xs => if p (pf | x, env) then Some_vt (x) else loop (pf | xs, p, env)
    | nil () => None_vt ()
  // end of [loop]
in
  loop (pf | xs, p, env)
end // end of [list_find__main]

implement{a}
list_find_fun {p:eff} (xs, f) = let
  val f = coerce (f) where { extern castfn
    coerce (f: a -<p> bool):<> (!unit_v | a, !ptr) -<p> bool
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_find__main<a> {..} {ptr} (pf | xs, f, null)
  prval unit_v () = pf
in
  ans
end // end of [list_find_fun]

implement{a}
list_find_clo
  {v} {p:eff} (pf1 | xs, f) = let
  typedef clo_t = (!v | a) -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | x: a, p_f: !ptr l_f):<p> bool = let
    prval (pf1, pf2) = pf; val ans = !p_f (pf1 | x); prval () = pf := (pf1, pf2)
  in
    ans
  end // end of [app]
  prval pf = (pf1, view@ f)
  val ans = list_find__main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = pf1 := pf.0
  prval () = view@ f := pf.1
in
  ans
end // end of [list_find_clo]

implement{a}
list_find_cloptr
  {v} {p:eff} (pf | xs, p) = let
  viewtypedef cloptr_t = (!v | a) -<cloptr,p> bool
  fn app (pf: !v | x: a, p: !cloptr_t):<p> bool = p (pf | x)
  val ans = list_find__main<a> {v} {cloptr_t} (pf | xs, app, p)
in
  ans
end // end of [list_find_cloptr]

implement{a}
list_find_cloref {p:eff} (xs, p) = let
  typedef cloref_t = a -<cloref,p> bool
  fn app (pf: !unit_v | x: a, p: !cloref_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_find__main<a> {unit_v} {cloref_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_find_cloref]

(* ****** ****** *)

(*
// HX: this one does not work out
macrodef list_fold_left_mac (list_fold_left, f, res, xs) = `(
  case+ ,(xs) of
  | x :: xs => ,(list_fold_left) (,(f), ,(f) (,(res), x), xs)
  | nil () => ,(res)
)
*)

implement{init}{a}
list_fold_left__main
  {v} {vt} {f:eff} (pf | f, res, xs, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | f: (!v | init, a, !vt) -<fun,f> init
    , res: init
    , xs: list (a, n)
    , env: !vt
  ) :<f> init = case+ xs of
    | x :: xs => let
        val res = f (pf | res, x, env) in loop (pf | f, res, xs, env)
      end // end of [::]
    | nil () => res
  // end of [loop]
in
  loop (pf | f, res, xs, env)
end // end of [list_fold_left__main]

implement{init}{a}
list_fold_left_fun {f:eff} (f, res, xs) = let
  val f = coerce (f) where { extern castfn
    coerce (f: (init, a) -<f> init):<> (!unit_v | init, a, !ptr) -<f> init
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_fold_left__main<init><a> {..} {ptr} (pf | f, res, xs, null)
  prval unit_v () = pf
in
  ans
end // end of [list_fold_left_fun]

implement{init}{a}
list_fold_left_clo
  {v:view} {f:eff} (pf1 | f, res, xs) = let
  viewtypedef clo_t = (!v | init, a) -<clo,f> init
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | res: init, x: a, p_f: !ptr l_f):<f> init = let
    prval (pf1, pf2) = pf; val ans = !p_f (pf1 | res, x); prval () = pf := (pf1, pf2)
  in
    ans
  end // end of [app]
  prval pf = (pf1, view@ f)
  val ans = list_fold_left__main<init><a> {V} {ptr l_f} (pf | app, res, xs, p_f)
  prval () = pf1 := pf.0
  prval () = view@ f := pf.1
in
  ans
end // end of [list_fold_left_clo]

implement{init}{a}
list_fold_left_cloptr
  {v:view} {f:eff} (pf | f, res, xs) = let
  viewtypedef cloptr_t = (!v | init, a) -<cloptr,f> init
  fn app (pf: !v | res: init, x: a, f: !cloptr_t):<f> init = f (pf | res, x)
  val ans = list_fold_left__main<init><a> {v} {cloptr_t} (pf | app, res, xs, f)
in
  ans
end // end of [list_fold_left_cloptr]

implement{init}{a}
list_fold_left_cloref {f:eff} (f, res, xs) = let
  typedef cloref_t = (init, a) -<cloref,f> init
  fn app (pf: !unit_v | res: init, x: a, f: !cloref_t):<f> init = f (res, x)
  prval pf = unit_v ()
  val ans = list_fold_left__main<init><a> {unit_v} {cloref_t} (pf | app, res, xs, f)
  prval unit_v () = pf
in
  ans
end // end of [list_fold_left_cloref]

(* ****** ****** *)

implement{init}{a1,a2}
list_fold2_left__main
  {v} {vt} {n} {f:eff} (pf | f, res, xs1, xs2, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | f: !(!v | init, a1, a2, !vt) -<fun,f> init
    , res: init
    , xs1: list (a1, n)
    , xs2: list (a2, n)
    , env: !vt
    ) :<f> init = case+ xs1 of
    | x1 :: xs1 => let
        val+ x2 :: xs2 = xs2; val res = f (pf | res, x1, x2, env)
      in
        loop (pf | f, res, xs1, xs2, env)
      end // end of [::]
    | nil () => res
  // end of [loop]
in
  loop (pf | f, res, xs1, xs2, env)
end // end of [list_fold2_left__main]

implement{init}{a1,a2}
list_fold2_left_cloptr
  {v} {n} {f:eff} (pf | f, res, xs1, xs2) = let
  viewtypedef cloptr_t = (!v | init, a1, a2) -<cloptr,f> init
  fn app (
      pf: !v | res: init, x1: a1, x2: a2, f: !cloptr_t
    ) :<f> init = f (pf | res, x1, x2)
  val ans = list_fold2_left__main<init><a1,a2> {v} {cloptr_t} (pf | app, res, xs1, xs2, f)
in
  ans
end // end of [list_fold2_left_cloptr]

implement{init}{a1,a2}
list_fold2_left_cloref {n} {f:eff} (f, res, xs1, xs2) = let
  typedef cloref_t = (init, a1, a2) -<cloref,f> init
  fn app (pf: !unit_v | res: init, x1: a1, x2: a2, f: !cloref_t):<f> init = f (res, x1, x2)
  prval pf = unit_v ()
  val ans = list_fold2_left__main<init><a1,a2> {unit_v} {cloref_t} (pf | app, res, xs1, xs2, f)
  prval unit_v () = pf
in
  ans
end // end of [list_fold2_left_cloref]

(* ****** ****** *)

implement{a}{sink}
list_fold_right__main
  {v} {vt} {f:eff} (pf | f, xs, res, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | f: (!v | a, sink, !vt) -<fun,f> sink
    , xs: list (a, n)
    , res: sink
    , env: !vt
    ) :<f> sink = case+ xs of
    | x :: xs => let
        val res = loop (pf | f, xs, res, env) in f (pf | x, res, env)
      end // end of [::]
    | nil () => res
  // end of [loop]
in
  loop (pf | f, xs, res, env)
end // end of [list_fold_right__main]

implement{a}{sink}
list_fold_right_fun {f:eff} (f, xs, res) = let
  val f = coerce (f) where { extern
    castfn coerce (f: (a, sink) -<f> sink):<> (!unit_v | a, sink, !ptr) -<f> sink
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_fold_right__main<a><sink> {..} {ptr} (pf | f, xs, res, null)
  prval unit_v () = pf
in
  ans
end // end of [list_fold_right_fun]

implement{a}{sink}
list_fold_right_clo
  {v:view} {f:eff} (pf1 | f, xs, res) = let
  viewtypedef clo_t = (!v | a, sink) -<clo,f> sink
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | x: a, res: sink, p_f: !ptr l_f):<f> sink = let
    prval (pf1, pf2) = pf; val ans = !p_f (pf1 | x, res); prval () = pf := (pf1, pf2)
  in
    ans
  end // end of [app]
  prval pf = (pf1, view@ f)
  val ans = list_fold_right__main<a><sink> {V} {ptr l_f} (pf | app, xs, res, p_f)
  prval () = pf1 := pf.0
  prval () = view@ f := pf.1
in
  ans
end // end of [list_fold_right_clo]

implement{a}{sink}
list_fold_right_cloptr
  {v:view} {f:eff} (pf | f, xs, res) = let
  viewtypedef cloptr_t = (!v | a, sink) -<cloptr,f> sink
  fn app (pf: !v | x: a, res: sink, f: !cloptr_t):<f> sink = f (pf | x, res)
  val ans = list_fold_right__main<a><sink> {v} {cloptr_t} (pf | app, xs, res, f)
in
  ans
end // end of [list_fold_right_cloptr]

implement{a}{sink}
list_fold_right_cloref {f:eff} (f, xs, res) = let
  typedef cloref_t = (a,sink) -<cloref,f> sink
  fn app (pf: !unit_v | x: a, res: sink, f: !cloref_t):<f> sink = f (x, res)
  prval pf = unit_v ()
  val ans = list_fold_right__main<a><sink> {unit_v} {cloref_t} (pf | app, xs, res, f)
  prval unit_v () = pf
in
  ans
end // end of [list_fold_right_cloref]

(* ****** ****** *)

implement{a1,a2}{sink}
list_fold2_right__main
  {v} {vt} {n} {f:eff} (pf | f, xs1, xs2, res, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | f: (!v | a1, a2, sink, !vt) -<fun,f> sink
    , xs1: list (a1, n)
    , xs2: list (a2, n)
    , res: sink
    , env: !vt
    ) :<f> sink = case+ xs1 of
    | x1 :: xs1 => let
        val+ x2 :: xs2 = xs2; val res = loop (pf | f, xs1, xs2, res, env)
      in
        f (pf | x1, x2, res, env)
      end // end of [::]
    | nil () => res
  // end of [loop]
in
  loop (pf | f, xs1, xs2, res, env)
end // end of [list_fold2_right__main]

(* ****** ****** *)

implement{a}
list_forall__main {v} {vt} {p:eff} (pf | xs, p, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | xs: list (a, n)
    , p: (!v | a, !vt) -<fun,p> bool
    , env: !vt
    ) :<p> bool = case+ xs of
    | x :: xs => begin
        if p (pf | x, env) then loop (pf | xs, p, env) else false
      end // end of [::]
    | nil () => false
  // end of [loop]
in
  loop (pf | xs, p, env)
end // end of [list_forall__main]

implement{a}
list_forall_fun {p:eff} (xs, p) = let
  val p = coerce (p) where {
    extern castfn coerce (p: a -<p> bool):<> (!unit_v | a, !ptr) -<p> bool
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_forall__main<a> {..} {ptr} (pf | xs, p, null)
  prval unit_v () = pf
in
  ans
end // end of [list_forall_fun]

implement{a}
list_forall_clo
  {v} {p:eff} (pf1 | xs, f) = let
  typedef clo_t = (!v | a) -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | x: a, p_f: !ptr l_f):<p> bool = let
    prval (pf1, pf2) = pf
    val ans = !p_f (pf1 | x)
    prval () = pf := (pf1, pf2)
  in
    ans
  end // end of [app]
  prval pf = (pf1, view@ f)
  val ans = list_forall__main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = pf1 := pf.0
  prval () = view@ f := pf.1
in
  ans
end // end of [list_forall_clo]

implement{a}
list_forall_cloptr
  {v} {p:eff} (pf | xs, p) = let
  viewtypedef cloptr_t = (!v | a) -<cloptr,p> bool
  fn app (pf: !v | x: a, p: !cloptr_t):<p> bool = p (pf | x)
  val ans = list_forall__main<a> {v} {cloptr_t} (pf | xs, app, p)
in
  ans
end // end of [list_forall_cloptr]

implement{a}
list_forall_cloref {p:eff} (xs, p) = let
  typedef cloref_t = a -<cloref,p> bool
  fn app (pf: !unit_v | x: a, p: !cloref_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_forall__main<a> {unit_v} {cloref_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_forall_cloref]

(* ****** ****** *)

implement{a1,a2}
list_forall2__main
  {v} {vt} {n} {p:eff} (pf | xs1, xs2, p, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | xs1: list (a1, n)
    , xs2: list (a2, n)
    , p: (!v | a1, a2, !vt) -<fun,p> bool
    , env: !vt
    ) :<p> bool = begin case+ xs1 of
    | x1 :: xs1 => let
        val+ x2 :: xs2 = xs2
      in
        if p (pf | x1, x2, env) then loop (pf | xs1, xs2, p, env) else false
      end
    | nil () => false
  end // end of [loop]
in
  loop (pf | xs1, xs2, p, env)
end // end of [list_forall2__main]

implement{a1,a2}
list_forall2_fun {n} {p:eff} (xs1, xs2, p) = let
  val p = coerce (p) where { extern castfn
    coerce (p: (a1, a2) -<p> bool):<> (!unit_v | a1, a2, !ptr) -<p> bool
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_forall2__main<a1,a2> {..} {ptr} (pf | xs1, xs2, p, null)
  prval unit_v () = pf
in
  ans
end // end of [list_forall2_fun]

implement{a1,a2}
list_forall2_clo
  {v} {n} {p:eff} (pf1 | xs1, xs2, f) = let
  typedef clo_t = (!v | a1, a2) -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | x1: a1, x2: a2, p_f: !ptr l_f):<p> bool = let
    prval (pf1, pf2) = pf; val ans = !p_f (pf1 | x1, x2); prval () = pf := (pf1, pf2)
  in
    ans
  end // end of [app]
  prval pf = (pf1, view@ f)
  val ans = list_forall2__main<a1,a2> {V} {ptr l_f} (pf | xs1, xs2, app, p_f)
  prval () = pf1 := pf.0
  prval () = view@ f := pf.1
in
  ans
end // end of [list_forall2_clo]

implement{a1,a2}
list_forall2_cloptr
  {v} {n} {p:eff} (pf | xs1, xs2, p) = let
  viewtypedef clo_t = (!v | a1, a2) -<cloptr,p> bool
  fn app (pf: !v | x1: a1, x2: a2, p: !clo_t):<p> bool = p (pf | x1, x2)
  val ans = list_forall2__main<a1,a2> {v} {clo_t} (pf | xs1, xs2, app, p)
in
  ans
end // end of [list_forall2_cloptr]

implement{a1,a2}
list_forall2_cloref {n} {p:eff} (xs1, xs2, p) = let
  viewtypedef clo_t = (a1, a2) -<cloref,p> bool
  fn app (pf: !unit_v | x1: a1, x2: a2, p: !clo_t):<p> bool = p (x1, x2)
  prval pf = unit_v ()
  val ans = list_forall2__main<a1,a2> {unit_v} {clo_t} (pf | xs1, xs2, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_forall2_cloref]

(* ****** ****** *)

implement{a}
list_foreach__main
  {v} {vt} {f:eff} (pf | xs, f, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | xs: list (a, n)
    , f: (!v | a, !vt) -<fun,f> void
    , env: !vt
    ) :<f> void = case+ xs of
    | x :: xs => (f (pf | x, env); loop (pf | xs, f, env))
    | nil () => ()
  // end of [loop]
in
  loop (pf | xs, f, env)
end // end of [list_foreach]

implement{a}
list_foreach_fun {f:eff} (xs, f) = let
  val f = coerce (f) where { extern castfn
    coerce (f: (a) -<f> void):<> (!unit_v | a, !ptr) -<f> void
  } // end of [where]
  prval pf = unit_v ()
  val () = list_foreach__main<a> {..} {ptr} (pf | xs, f, null)
  prval unit_v () = pf
in
  // empty
end // end of [list_foreach_fun]

implement{a}
list_foreach_clo {v} {f:eff} (pf1 | xs, f) = let
  typedef clo_t = (!v | a) -<clo,f> void
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | x: a, p_f: !ptr l_f):<f> void = () where {
    prval (pf1, pf2) = pf
    val () = !p_f (pf1 | x)
    prval () = pf := (pf1, pf2)
  } // end of [val]
  prval pf = (pf1, view@ f)
  val ans = list_foreach__main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = pf1 := pf.0 and () = view@ f := pf.1
in
  ans
end // end of [list_foreach_clo]

implement{a}
list_foreach_cloptr
  {v} {f:eff} (pf | xs, f) = let
  viewtypedef cloptr_t = (!v | a) -<cloptr,f> void
  fn app (pf: !v | x: a, f: !cloptr_t):<f> void = f (pf | x)
  val () = list_foreach__main<a> {v} {cloptr_t} (pf | xs, app, f)
in
  // empty
end // end of [list_foreach_cloptr]

implement{a}
list_foreach_cloref {f:eff} (xs, f) = let
  typedef cloref_t = (a) -<cloref,f> void
  fn app (pf: !unit_v | x: a, f: !cloref_t):<f> void = f (x)
  prval pf = unit_v ()
  val () = list_foreach__main<a> {unit_v} {cloref_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  // empty
end // end of [list_foreach_cloref]

(* ****** ****** *)

implement{a1,a2}
list_foreach2__main
  {v} {vt} {n} {f:eff} (pf | xs1, xs2, f, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | xs1: list (a1, n)
    , xs2: list (a2, n)
    , f: (!v | a1, a2, !vt) -<fun,f> void
    , env: !vt
    ) :<f> void = case+ xs1 of
    | x1 :: xs1 => let
        val x2 :: xs2 = xs2
      in
        f (pf | x1, x2, env); loop (pf | xs1, xs2, f, env)
      end
    | nil () => ()
  // end of [loop]
in
  loop (pf | xs1, xs2, f, env)
end // end of [list_foreach2__main]

implement{a1,a2}
list_foreach2_fun {n} {f} (xs, ys, f) = let
  val f = coerce (f) where { extern castfn
    coerce (f: (a1, a2) -<f> void):<> (!unit_v | a1, a2, !ptr) -<f> void
  } // end of [where]
  prval pf = unit_v ()
  val () = list_foreach2__main<a1,a2> {..} {ptr} (pf | xs, ys, f, null)
  prval unit_v () = pf
in
  // empty
end // end of [list_foreach2_fun]

implement{a1,a2}
list_foreach2_clo
  {v} {n} {f:eff} (pf1 | xs1, xs2, f) = let
  typedef clo_t = (!v | a1, a2) -<clo,f> void
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | x1: a1, x2: a2, p_f: !ptr l_f):<f> void = () where {
    prval (pf1, pf2) = pf
    val () = !p_f (pf1 | x1, x2)
    prval () = pf := (pf1, pf2)
  } // end of [val]
  prval pf = (pf1, view@ f)
  val () = list_foreach2__main<a1,a2> {V} {ptr l_f} (pf | xs1, xs2, app, p_f)
  prval () = pf1 := pf.0 and () = view@ f := pf.1
in
  // empty
end // end of [list_foreach2_clo]

implement{a1,a2}
list_foreach2_cloptr
  {v} {n} {f:eff} (pf | xs1, xs2, f) = let
  viewtypedef cloptr_t = (!v | a1, a2) -<cloptr,f> void
  fn app (pf: !v | x1: a1, x2: a2, f: !cloptr_t):<f> void =
    f (pf | x1, x2)
  val () = begin
    list_foreach2__main<a1,a2> {v} {cloptr_t} (pf | xs1, xs2, app, f)
  end // end of [val]
in
  // empty
end // end of [list_foreach2_cloptr]

implement{a1,a2}
list_foreach2_cloref {n} {f:eff} (xs1, xs2, f) = let
  typedef cloref_t = (a1, a2) -<cloref,f> void
  fn app (pf: !unit_v | x1: a1, x2: a2, f: !cloref_t):<f> void =
    f (x1, x2)
  prval pf = unit_v ()
  val () = begin
    list_foreach2__main<a1,a2> {unit_v} {cloref_t} (pf | xs1, xs2, app, f)
  end // end of [val]
  prval unit_v () = pf
in
  // empty
end // end of [list_foreach2_cloref]

(* ****** ****** *)

implement{a}
list_iforeach__main
  {v} {vt} {n} {f:eff} (pf | xs, f, env) = let
  viewtypedef cloptr_t = (!v | natLt n, a, !vt) -<fun,f> void
  fun loop {i,j:nat | i+j==n} .<j>. (
      pf: !v
    | i: int i
    , xs: list (a, j)
    , f: !cloptr_t
    , env: !vt
    ) :<f> void = begin case+ xs of
    | x :: xs => begin
        f (pf | i, x, env); loop (pf | i+1, xs, f, env)
      end // end of [::]
    | nil () => ()
  end // end of [loop]
in
  loop (pf | 0, xs, f, env)
end // end of [list_iforeach__main]

implement{a}
list_iforeach_fun {n} {f:eff} (xs, f) = let
  val f = coerce (f) where { extern castfn
    coerce (f: (natLt n, a) -<f> void):<> (!unit_v | natLt n, a, !ptr) -<f> void
  } // end of [where]
  prval pf = unit_v ()
  val () = list_iforeach__main<a> {unit_v} {ptr} (pf | xs, f, null)
  prval unit_v () = pf
in
  // empty
end // end of [list_iforeach_fun]

implement{a}
list_iforeach_clo {v} {n} {f:eff} (pf1 | xs, f) = let
  typedef clo_t = (!v | natLt n, a) -<clo,f> void
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | i: natLt n, x: a, p_f: !ptr l_f):<f> void = () where {
    prval (pf1, pf2) = pf
    val () = !p_f (pf1 | i, x)
    prval () = pf := (pf1, pf2)
  } // end of [val]
  prval pf = (pf1, view@ f)
  val () = list_iforeach__main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = pf1 := pf.0 and () = view@ f := pf.1
in
  // empty
end // end of [list_iforeach_clo]

(* ****** ****** *)

implement{a}
list_iforeach_cloptr
  {v} {n} {f:eff} (pf | xs, f) = let
  viewtypedef cloptr_t = (!v | natLt n, a) -<cloptr,f> void
  fn app (pf: !v | i: natLt n, x: a, f: !cloptr_t):<f> void = f (pf | i, x)
  val () = list_iforeach__main<a> {v} {cloptr_t} (pf | xs, app, f)
in
  // empty
end // end of [list_iforeach_cloptr]

(* ****** ****** *)

implement{a}
list_iforeach_cloref {n} {f:eff} (xs, f) = let
  typedef cloref_t = (natLt n, a) -<cloref,f> void
  fn app (pf: !unit_v | i: natLt n, x: a, f: !cloref_t):<f> void = f (i, x)
  prval pf = unit_v ()
  val () = list_iforeach__main<a> {unit_v} {cloref_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  // empty
end // end of [list_iforeach_cloref]

(* ****** ****** *)

implement{a1,a2}
list_iforeach2__main
  {v} {vt} {n} {f:eff} (pf | xs1, xs2, f, env) = let
  viewtypedef cloptr_t = (!v | natLt n, a1, a2, !vt) -<fun,f> void
  fun loop {i,j:nat | i+j==n} .<j>. (
      pf: !v
    | i: int i, xs1: list (a1, j), xs2: list (a2, j), f: !cloptr_t, env: !vt
    ) :<f> void = begin case+ (xs1, xs2) of
    | (x1 :: xs1, x2 :: xs2) => begin
        f (pf | i, x1, x2, env); loop (pf | i+1, xs1, xs2, f, env)
      end // end of [::, ::]
    | (nil (), nil ()) => ()
  end // end of [loop]
in
  loop (pf | 0, xs1, xs2, f, env)
end // end of [list_iforeach2__main]

implement{a1,a2}
list_iforeach2_fun {n} {f} (xs, ys, f) = let
  val f = coerce (f) where { extern castfn
    coerce (f: (natLt n, a1, a2) -<f> void)
      :<> (!unit_v | natLt n, a1, a2, !ptr) -<f> void
  } // end of [where]
  prval pf = unit_v ()
  val () = list_iforeach2__main {unit_v} {ptr} (pf | xs, ys, f, null)
  prval unit_v () = pf
in
  // empty
end // end of [list_foreach2_fun]

implement{a1,a2}
list_iforeach2_clo
  {v} {n} {f:eff} (pf1 | xs1, xs2, f) = let
  typedef clo_t = (!v | natLt n, a1, a2) -<clo,f> void
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | i: natLt n, x1: a1, x2: a2, p_f: !ptr l_f):<f> void = () where {
    prval (pf1, pf2) = pf
    val () = !p_f (pf1 | i, x1, x2)
    prval () = pf := (pf1, pf2)
  } // end of [val]
  prval pf = (pf1, view@ f)
  val ans = list_iforeach2__main<a1,a2> {V} {ptr l_f} (pf | xs1, xs2, app, p_f)
  prval () = pf1 := pf.0 and () = view@ f := pf.1
in
  ans
end // end of [list_iforeach2_clo]

implement{a1,a2}
list_iforeach2_cloptr
  {v} {n} {f:eff} (pf | xs1, xs2, f) = let
  viewtypedef cloptr_t = (!v | natLt n, a1, a2) -<cloptr,f> void
  fn app (pf: !v | i: natLt n, x1: a1, x2: a2, f: !cloptr_t):<f> void =
    f (pf | i, x1, x2)
  val () = begin
    list_iforeach2__main<a1,a2> {v} {cloptr_t} (pf | xs1, xs2, app, f)
  end // end of [val]
in
  // empty
end // end of [list_iforeach2_cloptr]

implement{a1,a2}
list_iforeach2_cloref {n} {f:eff} (xs1, xs2, f) = let
  viewtypedef cloref_t = (natLt n, a1, a2) -<cloref,f> void
  fn app (pf: !unit_v | i: natLt n, x1: a1, x2: a2, f: !cloref_t):<f> void =
    f (i, x1, x2)
  prval pf = unit_v ()
  val () = begin
    list_iforeach2__main<a1,a2> {unit_v} {cloref_t} (pf | xs1, xs2, app, f)
  end // end of [val]
  prval unit_v () = pf
in
  // empty
end // end of [list_iforeach2_cloref]

(* ****** ****** *)

implement{a}
list_get_elt_at (xs, i) = let
  fun loop {n,i:nat | i < n} .<n>.
    (xs: list (a, n), i: int i):<> a = let
    val x :: xs = xs
  in
    if i > 0 then loop (xs, i - 1) else x
  end // end of [loop]
in
  loop (xs, i)
end // end of [list_get_elt_at]

implement{a}
list_nth (xs, i) = list_get_elt_at<a> (xs, i)

implement{a}
list_get_elt_at_exn (xs, i) = let
  fun loop {n,i:nat} .<n>. 
    (xs: list (a, n), i: int i):<!exn> [n>0] a =
    case+ xs of
    | x :: xs => if i > 0 then loop (xs, i - 1) else x
    | nil () => $raise ListSubscriptException ()
  // end of [loop]
in
  loop (xs, i)
end // end of [list_get_elt_at_exn]

implement{a}
list_nth_exn (xs, i) = list_get_elt_at_exn<a> (xs, i)

implement{a}
list_get_elt_at_opt (xs, i) = let
  fun loop {n,i:nat} .<n>.
    (xs: list (a, n), i: int i):<> Option_vt a =
    case+ xs of
    | x :: xs => if i > 0 then loop (xs, i - 1) else Some_vt x
    | nil () => None_vt ()
  // end of [loop]
in
  loop (xs, i)
end // end of [list_get_elt_at_opt]

implement{a}
list_nth_opt (xs, n) = list_get_elt_at_opt<a> (xs, n)

(* ****** ****** *)

implement{a}
list_head (xs) = let val x :: _ = xs in x end
implement{a}
list_head_exn (xs) = case xs of
  | x :: _ => x | nil () => $raise ListSubscriptException
// end of [list_hean_exn]

(* ****** ****** *)

implement{}
list_is_empty {a} (xs) = begin
  case+ xs of cons _ => false | nil _ => true
end // end of [list_is_empty]

implement{}
list_isnot_empty {a} (xs) = begin
  case+ xs of _ :: _ => true | nil () => false
end // end of [list_is_not_empty]

(* ****** ****** *)

implement{a}
list_last (xs0) = loop (x, xs) where {
  fun loop {n:nat} .<n>.
    (x0: a, xs: list (a, n)):<> a = case+ xs of
    | list_cons (x, xs) => loop (x, xs) | list_nil () => x0
  // end of [loop]
  val+ list_cons (x, xs) = xs0
} // end of [list_last]

implement{a}
list_last_exn (xs) = case+ xs of
  | _ :: _ => list_last (xs) | nil () => begin
      $raise ListSubscriptException
    end // end of [nil]
// end of [list_last_exn]

(* ****** ****** *)

implement{a}
list_length (xs) = let
  fun loop {i,j:nat} .<i>.
    (xs: list (a, i), j: int j):<> int (i+j) = begin
    case+ xs of  _ :: xs => loop (xs, isucc j) | nil () => j
  end // end of [loop]
in
  loop (xs, 0)
end // end of [list_length]

(* ****** ****** *)

implement{a}{b}
list_map__main
  {v} {vt} {n} {f:eff} (pf | xs, f, env) = let
  typedef fun_t = (!v | a, !vt) -<fun,f> b
  fun loop {n:nat} .<n>. (
      pf: !v
    | xs: list (a, n)
    , f: fun_t
    , res: &(List_vt b)? >> list_vt (b, n)
    , env: !vt
    ) :<f> void = begin case+ xs of
    | x :: xs => let
        val y = f (pf | x, env)
        val+ () = (res := list_vt_cons {b} {0} (y, ?)); val+ list_vt_cons (_, !p) = res
      in
        loop (pf | xs, f, !p, env); fold@ res
      end // end of [::]
    | nil () => (res := list_vt_nil ())
  end // end of [loop]
  var res: List_vt b // uninitialized
in
  loop (pf | xs, f, res, env); res
end // end of [list_map__main]

implement{a}{b}
list_map_fun {n:int} {f:eff} (xs, f) = let
  val f = coerce (f) where {
    extern castfn coerce (f: a -<f> b):<> (!unit_v | a, !ptr) -<f> b
  } // end of [where]
  prval pf = unit_v ()
  val ys = list_map__main<a><b> {..} {ptr} (pf | xs, f, null)
  prval unit_v () = pf
in
  ys
end // end of [list_map_fun]

implement{a}{b}
list_map_clo
  {v} {n:int} {f:eff} (pf1 | xs, f) = let
  viewtypedef clo_t = (!v | a) -<clo,f> b
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | x: a, p_f: !ptr l_f):<f> b = let
    prval (pf1, pf2) = pf
    val ans = !p_f (pf1 | x)
    prval () = pf := (pf1, pf2)
  in
    ans
  end // end of [app]
  prval pf = (pf1, view@ f)
  val ys = list_map__main<a><b> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = pf1 := pf.0
  prval () = view@ f := pf.1
in
  ys
end // end of [list_map_clo]

implement{a}{b}
list_map_cloptr
  {v} {n:int} {f:eff} (pf | xs, f) = let
  viewtypedef cloptr_t = (!v | a) -<cloptr,f> b
  fn app (pf: !v | x: a, f: !cloptr_t):<f> b = f (pf | x)
  val ys = list_map__main<a><b> {v} {cloptr_t} (pf | xs, app, f)
in
  ys
end // end of [list_map_cloptr]

implement{a}{b}
list_map_cloref {n:int} {f:eff} (xs, f) = let
  typedef cloref_t = a -<cloref,f> b
  fn app (pf: !unit_v | x: a, f: !cloref_t):<f> b = f (x)
  prval pf = unit_v ()
  val ys = list_map__main<a><b> {unit_v} {cloref_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  ys
end // end of [list_map_cloref]

(* ****** ****** *)

implement{a1,a2}{b}
list_map2__main
  {v:view} {vt:viewtype} {n} {f:eff} (pf | xs, ys, f, env) = let
  var res: List_vt b? // uninitialized
  fun loop {n:nat} .<n>. (
      pf: !v
    | xs: list (a1, n)
    , ys: list (a2, n)
    , f: (!v | a1, a2, !vt) -<fun,f> b
    , res: &(List_vt b)? >> list_vt (b, n)
    , env: !vt
  ) :<f> void = begin case+ (xs, ys) of
    | (x :: xs, y :: ys) => let
        val z = f (pf | x, y, env)
        val+ () = (res := list_vt_cons {b} {0} (z, ?))
        val+ list_vt_cons (_, !p_res1) = res
      in
        loop (pf | xs, ys, f, !p_res1, env); fold@ res
      end
    | (nil (), nil ()) => (res := list_vt_nil ())
  end // end of [loop]
in
  loop (pf | xs, ys, f, res, env); res
end // end of [list_map2__main]

implement{a1,a2}{b}
list_map2_fun {n} {f:eff} (xs, ys, f) = let
  val f = coerce (f) where { extern castfn
    coerce (f: (a1, a2) -<f> b):<> (!unit_v | a1, a2, !ptr) -<f> b
  } // end of [where]
  prval pf = unit_v ()
  val zs = list_map2__main<a1,a2><b> {..} {ptr} (pf | xs, ys, f, null)
  prval unit_v () = pf
in
  zs
end // end of [list_map2_fun]

implement{a1,a2}{b}
list_map2_clo
  {v} {n} {f:eff} (pf1 | xs1, xs2, f) = let
  typedef clo_t = (!v | a1, a2) -<clo,f> b
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | x1: a1, x2: a2, p_f: !ptr l_f):<f> b = let
    prval (pf1, pf2) = pf
    val ans = !p_f (pf1 | x1, x2)
    prval () = pf := (pf1, pf2)
  in
    ans
  end // end of [app]
  prval pf = (pf1, view@ f)
  val ans = list_map2__main<a1,a2><b> {V} {ptr l_f} (pf | xs1, xs2, app, p_f)
  prval () = pf1 := pf.0
  prval () = view@ f := pf.1
in
  ans
end // end of [list_map2_clo]

implement{a1,a2}{b}
list_map2_cloptr
  {v} {n} {f:eff} (pf | xs, ys, f) = let
  viewtypedef cloptr_t = (!v | a1, a2) -<cloptr,f> b
  fn app (pf: !v | x: a1, y: a2, f: !cloptr_t):<f> b = f (pf | x, y)
  val zs = begin
    list_map2__main<a1,a2><b> {v} {cloptr_t} (pf | xs, ys, app, f)
  end // end of [val]
in
  zs
end  // end of [list_map2_cloptr]

implement{a1,a2}{b}
list_map2_cloref {n} {f:eff} (xs, ys, f) = let
  typedef cloref_t = (a1, a2) -<cloref,f> b
  fn app (pf: !unit_v | x: a1, y: a2, f: !cloref_t):<f> b = f (x, y)
  prval pf = unit_v ()
  val zs = begin
    list_map2__main<a1,a2><b> {unit_v} {cloref_t} (pf | xs, ys, app, f)
  end // end of [val]
  prval unit_v () = pf
in
  zs
end  // end of [list_map2_cloref]

(* ****** ****** *)

implement{a}
list_reverse_append (xs, ys) = let
  fun loop {n1,n2:nat} .<n1>.
    (xs: list (a, n1), ys: list (a, n2)):<> list (a, n1+n2) =
    case+ xs of x :: xs => loop (xs, x :: ys) | nil () => ys
in
  loop (xs, ys)
end // end of [list_reverse_append]

(* ****** ****** *)

implement{a}
list_reverse (xs) =
  list_reverse_append_vt<a> (xs, list_vt_nil ())
// end of [list_reverse]

implement{a}
list_reverse_append_vt (xs, ys) = let
  fun loop {n1,n2:nat} .<n1>.
    (xs: list (a, n1), ys: list_vt (a, n2)):<> list_vt (a, n1+n2) =
    case+ xs of x :: xs => loop (xs, list_vt_cons (x, ys)) | nil () => ys
in
  loop (xs, ys)
end (* end of [list_reverse] *)

(* ****** ****** *)

implement{a}
list_set_elt_at (xs, i, x0) = let
  var res: List a // uninitialized
  fun loop {n,i:nat | i < n} .<n>.
    (xs: list (a, n), i: int i, x0: a, res: &(List a)? >> list (a, n))
    :<> void = let
    val x :: xs = xs in
    if i > 0 then let
      val () = (res := cons {a} {0} (x, ?))
      val+ cons (_, !p) = res
    in
      loop (xs, i-1, x0, !p); fold@ res
    end else begin
      res := cons (x0, xs)
    end
  end // end of [loop]
in
  loop (xs, i, x0, res); res
end // end of [list_set_elt_at]

local

fun{a:t@ype} aux_test {n,i:nat} .<n>.
  (xs: list (a, n), i: int i):<> bool (i < n) = begin
  case+ xs of
  | x :: xs => if i > 0 then aux_test (xs, i-1) else true
  | nil () => false
end // end of [aux_test]

in

implement{a}
list_set_elt_at_exn (xs, i, x0) =
  if aux_test<a> (xs, i) then list_set_elt_at (xs, i, x0)
  else $raise ListSubscriptException

implement{a}
list_set_elt_at_opt (xs, i, x0) =
  if aux_test<a> (xs, i) then Some_vt (list_set_elt_at (xs, i, x0))
  else None_vt ()

end // end of [local]

(* ****** ****** *)

implement{a}
list_split_at {n,i} (xs, i) = let
  var fsts: List_vt a? // uninitialized
  fun loop {j:nat | j <= i} .<i-j>.
    (xs: list (a, n-j), ij: int (i-j), fsts: &(List_vt a)? >> list_vt (a, i-j))
    :<> list (a, n-i) =
    if ij > 0 then let
      val+ x :: xs = xs
      val () = (fsts := list_vt_cons {a} {0} (x, ?)); val+ list_vt_cons (_, !p) = fsts
      val snds = loop {j+1} (xs, ij - 1, !p)
    in
      fold@ fsts; snds
    end else begin
      fsts := list_vt_nil (); xs
    end
  val snds = loop {0} (xs, i, fsts)
in
  (fsts, snds)
end // end of [list_split_at]

(* ****** ****** *)

implement{a}
list_tail (xs) = let val _ :: xs = xs in xs end
implement{a}
list_tail_exn (xs) = case+ xs of
  | _ :: xs => xs | nil () => $raise ListSubscriptException

(* ****** ****** *)

implement{a}
list_take (xs, i) = let
  var res: List_vt a // uninitialized
  fun loop {n,i:nat | i <= n} .<i>.
    (xs: list (a, n), i: int i, res: &(List_vt a)? >> list_vt (a, i)):<> void =
    if i > 0 then let
      val x :: xs = xs
      val () = (res := list_vt_cons {a} {0} (x, ?))
      val+ list_vt_cons (_, !p) = res
    in
      loop (xs, i-1, !p); fold@ res
    end else begin
      res := list_vt_nil ()
    end (* end of [loop] *)
  // end of [loop]
in
  loop (xs, i, res); res
end // end of [list_take]

implement{a}
list_take_exn {n,i} (xs, i) = let
  fun loop {n,i:nat} .<i>.
    (xs: list (a, n), i: int i, res: &List_vt a? >> list_vt (a, j))
    :<> #[j:nat | (i <= n && i == j) || (n < i && n == j)] bool (n < i)  =
    if i > 0 then begin case+ xs of
      | list_cons (x, xs) =>
          (fold@ res; ans) where {
          val () = res := list_vt_cons {a} {0} (x, ?)
          val+ list_vt_cons (_, !p_res1) = res
          val ans = loop (xs, i-1, !p_res1)
        } // end of [list_cons]
      | list_nil () => (res := list_vt_nil (); true(*err*))
    end else begin
      res := list_vt_nil (); false(*err*)
    end (* end of [if] *)
  // end of [loop]    
  var res: List_vt a? // uninitialized
  val err = loop {n,i} (xs, i, res)
in
  if err then let
    val () = list_vt_free res in $raise ListSubscriptException ()
  end else begin
    res // i <= n && length (res) == i
  end (* end of [if] *)
end (* end of [list_take_exn] *)

(* ****** ****** *)

implement{a,b}
list_zip (xs, ys) = let
  typedef ab = @(a, b)
  var res: List_vt ab // uninitialized
  fun loop {i:nat} .<i>.
    (xs: list (a, i), ys: list (b, i), res: &(List_vt ab)? >> list_vt (ab, i)):<> void =
    case+ (xs, ys) of
    | (x :: xs, y :: ys) => let
        val () = (res := list_vt_cons {ab} {0} (@(x, y), ?)); val+ list_vt_cons (_, !p) = res
      in
        loop (xs, ys, !p); fold@ res
      end // end of [::, ::]
    | (nil (), nil ()) => (res := list_vt_nil ())
in
  loop (xs, ys, res); res
end // end of [list_zip]

(* ****** ****** *)

implement{a1,a2}{b}
list_zipwth_fun
  (xs, ys, f) = list_map2_fun<a1,a2><b> (xs, ys, f)
// end of [list_zipwth_fun]

implement{a1,a2}{b}
list_zipwth_clo
  (pf | xs, ys, f) = list_map2_clo<a1,a2><b> (pf | xs, ys, f)
// end of [list_zipwth_clo]

implement{a1,a2}{b}
list_zipwth_cloptr
  (pf | xs, ys, f) = list_map2_cloptr<a1,a2><b> (pf | xs, ys, f)
// end of [list_zipwth_cloptr]

implement{a1,a2}{b}
list_zipwth_cloref
  (xs, ys, f) = list_map2_cloref<a1,a2><b> (xs, ys, f)
// end of [list_zipwth_cloref]

(* ****** ****** *)

implement{a1,a2}
list_unzip xys = let
  var res1: List_vt a1 and res2: List_vt a2 // uninitialized
  fun loop {n:nat} .<n>. (
      xys: list (@(a1, a2), n)
    , res1: &(List_vt a1)? >> list_vt (a1, n)
    , res2: &(List_vt a2)? >> list_vt (a2, n)
  ) :<> void = begin case+ xys of
    | xy :: xys => let
        val () = (res1 := list_vt_cons {a1} {0} (xy.0, ?)); val+ list_vt_cons (_, !p1) = res1
        val () = (res2 := list_vt_cons {a2} {0} (xy.1, ?)); val+ list_vt_cons (_, !p2) = res2
      in
        loop (xys, !p1, !p2); fold@ res1; fold@ res2
      end
    | nil () => (res1 := list_vt_nil (); res2 := list_vt_nil ())
  end // end of [loop]
in
  loop (xys, res1, res2); (res1, res2)
end // end of [list_unzip]

(* ****** ****** *)

//
// HX: implementing merge sort
//

(*
**
** llist(a, i, n): a list of lists such that
**   1. the sum of the lengths of lists in the list of lists is i, and
**   2. the length of the list is n.
**
*)

local
//
// HX: this is not an efficient implementation but it is guaranteed to be O(n*log(n))
//
  datatype llist (a:t@ype+, int, int) =
    | {i,j,n:nat} lcons (a, i+j, n+1) of (list (a, i), llist (a, j, n))
    | lnil (a, 0, 0)

  typedef lte (a:t@ype, env: viewtype, f:eff) = (a, a, !env) -<fun,f> bool

  fun{a:t@ype} aux1
    {env:viewtype} {i:nat} {f:eff} .<i>.
    (lte: lte (a, env, f), xs: list (a, i), env: !env)
    :<f> [n:nat] llist (a, i, n) = case+ xs of
    | x1 :: x2 :: xs => let
        val l = (
          if lte (x1, x2, env) then x1 :: x2 :: nil else x2 :: x1 :: nil
        ) : list (a, 2)
      in
         lcons (l, aux1 (lte, xs, env))
      end
    | l as list_cons (x, list_nil ()) => lcons (l, lnil ())
    | nil () => lnil
  // end of [aux1]

  fun{a:t@ype} aux2
    {env:viewtype} {i,j:nat} {f:eff} .<i+j>. (
      lte: lte (a, env, f), xs: list (a, i), ys: list (a, j), env: !env
    ) :<f> list (a, i+j) = begin
    case+ (xs, ys) of
    | (xs as x :: xs', ys as y :: ys') => begin
        if lte (x, y, env) then begin
          x :: aux2 (lte, xs', ys, env)
        end else begin
          y :: aux2 (lte, xs, ys', env)
        end
      end // end of [::, ::]
    | (xs, nil ()) => xs
    | (nil (), ys) => ys
  end // end of [aux2]
  // end of [aux2]

  fun{a:t@ype} aux3
    {env:viewtype} {i,n:nat} {f:eff} .<n>.
    (lte: lte (a, env, f), xss: llist (a, i, n), env: !env)
    :<f> [n1:nat | (n < 2 && n1 == n) || n1 < n] llist (a, i, n1) =
    case+ xss of
    | lcons (xs1, lcons (xs2, xss)) => begin
        lcons (aux2 (lte, xs1, xs2, env), aux3 (lte, xss, env))
      end
    | _ =>> xss
  // end of [aux3]

  fun{a:t@ype} aux4
    {env:viewtype} {i,n:nat} {f:eff} .<n>.
    (lte: lte (a, env, f), xss: llist (a, i, n), env: !env)
    :<f> list (a, i) = begin case+ xss of
    | lnil () => nil ()
    | lcons (xs, lnil ()) => xs
    | _ =>> begin
        aux4 (lte, aux3 (lte, xss, env), env)
      end
  end // end of [aux4]

in // in of [local]

implement{a}
list_mergesort (xs, lte, env) = aux4 (lte, aux1 (lte, xs, env), env)

end // end of [local]

(* ****** ****** *)

//
// HX: implementing quick sort
//

local
//
// this may not be a practical implementation as it can easily be O(n*n)
//
  typedef lte (a:t@ype, env: viewtype, f:eff) = (a, a, !env) -<fun,f> bool

  fun{a:t@ype}
  qsrt {env:viewtype}
    {n:nat} {f:eff} .<n,0>.
    (lte: lte (a, env, f), xs: list (a, n), env: !env)
    :<f> list (a, n) = begin
    case+ xs of // [case+]: exhaustive pattern matching
    | x' :: xs' => begin
        part {env} {n-1,0,0} (lte, x', xs', nil, nil, env)
      end // end of [::]
    | nil () => nil ()
  end // end of [qsrt]

  and part {env:viewtype}
    {p,l,r:nat} {f:eff} .<p+l+r,p+1>. (
      lte: lte (a, env, f)
    , x: a, xs: list (a, p)
    , l: list (a, l), r: list (a, r)
    , env: !env
    ) :<f> list (a, p+l+r+1) = begin
    case+ xs of // case+ mandates exhaustive pattern matching
    | x' :: xs' => begin
        if lte (x', x, env) then begin
          part {env} {p-1,l+1,r} (lte, x, xs', x' :: l, r, env)
        end else begin
          part {env} {p-1,l,r+1} (lte, x, xs', l, x' :: r, env)
        end // end of [if]
      end (* end of [::] *)
    | nil () => begin
        list_append (qsrt (lte, l, env), x :: qsrt (lte, r, env))
      end // end of [nil]
  end // end of [part]

in // end of [local]

implement{a}
list_quicksort (xs, lte, env) = qsrt (lte, xs, env)

end // end of [local]

(* ****** ****** *)

// [list.sats] is already loaded by a call to [pervasive_load]
staload _(*anonymous*) = "prelude/SATS/list.sats" // this forces that the static
// loading function for [list.sats] is to be called at run-time
// this is really needed only if some datatypes are declared in [list.sats]

(* ****** ****** *)

(* end of [list.dats] *)
