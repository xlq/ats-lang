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

#define ATS_DYNLOADFLAG 0 // loaded by [ats_main_prelude]

(* ****** ****** *)

// list implementation

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

// this is a proof function
implement list_length_is_nonnegative (xs) =
  case+ xs of list_cons _ => () | list_nil () => ()

(* ****** ****** *)

// this is a casting function
implement list_of_list_vt {a} (xs) = aux (xs) where {
  castfn aux {n:nat} .<n>. (xs: list_vt (a, n)):<> list (a, n) =
    case+ xs of
    | ~list_vt_cons (x, xs) => list_cons (x, aux xs)
    | ~list_vt_nil () => list_nil ()
} // end of [list_of_list_vt]

(* ****** ****** *)

implement{a} list_of_arraysize (arrsz) =
  list_of_list_vt (list_vt_of_arraysize<a> arrsz)

(* ****** ****** *)

implement{a} list_app__main
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

implement{a} list_app_fun {n:int} {f:eff} (xs, f) = let
  val f = coerce (f) where {
    extern castfn coerce (f: a -<f> void):<> (!unit_v | a, !Ptr) -<f> void
  } // end of [where]
  prval pf = unit_v ()
  val () = list_app__main (pf | xs, f, null)
  prval unit_v () = pf
in
  ()
end // end of [list_app_fun]

implement{a} list_app_clo {n:int} {f:eff} (xs, f) = let
  viewtypedef clo_t = a -<clo,f> void
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x: a, p_f: !ptr l_f):<f> void = !p_f (x)
  prval pf = view@ f
  val () = list_app__main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = view@ f := pf
in
  ()
end // end of [list_app_clo]

implement{a} list_app_cloptr {n:int} {f:eff} (xs, f) = let
  viewtypedef cloptr_t = a -<cloptr,f> void
  fn app (pf: !unit_v | x: a, f: !cloptr_t):<f> void = f (x)
  prval pf = unit_v ()
  val () = list_app__main<a> {unit_v} {cloptr_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  ()
end // end of [list_app_cloptr]

implement{a} list_app_cloref {n:int} {f:eff} (xs, f) = let
  typedef cloref_t = a -<cloref,f> void
  fn app (pf: !unit_v | x: a, f: !cloref_t):<f> void = f (x)
  prval pf = unit_v ()
  val () = list_app__main<a> {unit_v} {cloref_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  ()
end // end of [list_app_cloref]

(* ****** ****** *)

implement{a1,a2} list_app2__main
  {v:view} {vt:viewtype} {n} {f:eff} (pf | xs1, xs2, f, env) = let
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

implement{a1,a2} list_app2_fun {n} {f:eff} (xs1, xs2, f) = let
  val f = coerce (f) where { extern castfn
    coerce (f: (a1, a2) -<f> void):<> (!unit_v | a1, a2, !Ptr) -<f> void
  } // end of [where]
  prval pf = unit_v ()
  val () = list_app2__main (pf | xs1, xs2, f, null)
  prval unit_v () = pf
in
  // empty
end // end of [list_app2_fun]

implement{a1,a2} list_app2_clo {n} {f:eff} (xs1, xs2, f) = let
  typedef clo_t = (a1, a2) -<clo,f> void
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x1: a1, x2: a2, p_f: !ptr l_f):<f> void = !p_f (x1, x2)
  prval pf = view@ f
  val () = list_app2__main<a1,a2> {V} {ptr l_f} (pf | xs1, xs2, app, p_f)
  prval () = view@ f := pf
in
  // empty
end // end of [list_app2_clo]

implement{a1,a2} list_app2_cloptr {n} {f:eff} (xs1, xs2, f) = let
  viewtypedef cloptr_t = (a1, a2) -<cloptr,f> void
  fn app (pf: !unit_v | x1: a1, x2: a2, f: !cloptr_t):<f> void = f (x1, x2)
  prval pf = unit_v ()
  val () = begin
    list_app2__main<a1,a2> {unit_v} {cloptr_t} (pf | xs1, xs2, app, f)
  end // end of [val]
  prval unit_v () = pf
in
  // empty
end  // end of [list_app2_cloptr]

implement{a1,a2} list_app2_cloref {n} {f:eff} (xs1, xs2, f) = let
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

implement{a} list_append {i,j} (xs, ys) = let
  var res: List a // uninitialized
  fun loop {n1,n2:nat} .<n1>.
    (xs: list (a, n1), ys: list (a, n2), res: &(List a)? >> list (a, n1+n2))
    :<> void = begin case+ xs of
    | x :: xs => let
        val () = (res := cons {a} {0} (x, ?)); val cons (_, !p) = res
      in
        loop (xs, ys, !p); fold@ res
      end
    | nil () => (res := ys)
  end // end of [loop]
in
  loop (xs, ys, res); res
end // end of [list_append]

(*

// standard non-tail-recursive implementation of list-append

implement{a} list_append {i,j} (xs, ys) = let
  fun aux {n1,n2:nat} .<n1>.
    (xs: list (a, n1), ys: list (a, n2)):<> list (a, n1+n2) =
    case+ xs of x :: xs => x :: aux (xs, ys) | nil () => ys
in
  aux (xs, ys)
end

*)

(* ****** ****** *)

implement{a1,a2} list_assoc__main {v} {vt} {eq:eff} (pf | xys, eq, x0, env) = let
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

implement{a1,a2} list_assoc_fun {eq:eff} (xys, eq, x0) = let
  val eq = coerce (eq) where { extern castfn
    coerce (eq: (a1, a1) -<eq> bool):<> (!unit_v | a1, a1, !Ptr) -<eq> bool
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_assoc__main (pf | xys, eq, x0, null)
  prval unit_v () = pf
in
  ans
end // end of [list_assoc_fun]

implement{a1,a2} list_assoc_clo {eq:eff} (xys, eq, x0) = let
  typedef clo_t = (a1, a1) -<clo,eq> bool
  stavar l_eq: addr; val p_eq: ptr l_eq = &eq
  viewdef V = clo_t @ l_eq
  fn app (pf: !V | x: a1, y: a1, p_eq: !ptr l_eq):<eq> bool = !p_eq (x, y)
  prval pf = view@ eq
  val ans = list_assoc__main<a1,a2> {V} {ptr l_eq} (pf | xys, app, x0, p_eq)
  prval () = view@ eq := pf
in
  ans
end // end of [list_assoc_clo]

implement{a1,a2} list_assoc_cloptr {eq:eff} (xys, eq, x0) = let
  viewtypedef cloptr_t = (a1, a1) -<cloptr,eq> bool
  fn app (pf: !unit_v | x: a1, y: a1, eq: !cloptr_t):<eq> bool = eq (x, y)
  prval pf = unit_v ()
  val ans = list_assoc__main<a1,a2> {unit_v} {cloptr_t} (pf | xys, app, x0, eq)
  prval unit_v () = pf
in
  ans
end // end of [list_assoc_cloptr]

implement{a1,a2} list_assoc_cloref {eq:eff} (xys, eq, x0) = let
  typedef cloref_t = (a1, a1) -<cloref,eq> bool
  fn app (pf: !unit_v | x: a1, y: a1, eq: !cloref_t):<eq> bool = eq (x, y)
  prval pf = unit_v ()
  val ans = list_assoc__main<a1,a2> {unit_v} {cloref_t} (pf | xys, app, x0, eq)
  prval unit_v () = pf
in
  ans
end // end of [list_assoc_cloref]

(* ****** ****** *)

implement{a} list_concat (xss) = let
  fun aux {n:nat} .<n>.
    (xs0: List a, xss: list (List a, n)):<> List a =
    case+ xss of
    | xs :: xss => list_append (xs0, aux (xs, xss))
    | nil () => xs0
in
  case+ xss of xs :: xss => aux (xs, xss) | nil () => nil ()
end // end of [list_concat]

//

implement{a} list_drop (xs, i) = let
  fun loop {n,i:nat | i <= n} .<i>.
    (xs: list (a, n), i: int i):<> list (a, n-i) =
    if i > 0 then let val _ :: xs = xs in loop (xs, i-1) end
    else xs
in
  loop (xs, i)
end // end of [list_drop]

(* ****** ****** *)

implement{a} list_exists__main {v} {vt} {p:eff} (pf | xs, p, env) = let
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

implement{a} list_exists_fun {p:eff} (xs, p) = let
  val p = coerce (p) where {
    extern castfn coerce (p: a -<p> bool):<> (!unit_v | a, !Ptr) -<p> bool
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_exists__main (pf | xs, p, null)
  prval unit_v () = pf
in
  ans
end // end of [list_exists_fun]

implement{a} list_exists_clo {p:eff} (xs, f) = let
  typedef clo_t = a -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x: a, p_f: !ptr l_f):<p> bool = !p_f (x)
  prval pf = view@ f
  val ans = list_exists__main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_exists_clo]

implement{a} list_exists_cloptr {p:eff} (xs, p) = let
  viewtypedef cloptr_t = a -<cloptr,p> bool
  fn app (pf: !unit_v | x: a, p: !cloptr_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_exists__main<a> {unit_v} {cloptr_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_exists_cloptr]

implement{a} list_exists_cloref {p:eff} (xs, p) = let
  typedef cloref_t = a -<cloref,p> bool
  fn app (pf: !unit_v | x: a, p: !cloref_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_exists__main<a> {unit_v} {cloref_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_exists_cloref]

(* ****** ****** *)

implement{a1,a2} list_exists2__main
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
        if p (pf | x1, x2, env) then true else loop (pf | xs1, xs2, p, env)
      end (* end of [::] *)
    | nil () => false
  end // end of [loop]
in
  loop (pf | xs1, xs2, p, env)
end // end of [list_exists2__main]

implement{a1,a2} list_exists2_fun {n} {p:eff} (xs1, xs2, p) = let
  val p = coerce (p) where {
    extern castfn coerce (p: (a1, a2) -<p> bool):<> (!unit_v | a1, a2, !Ptr) -<p> bool
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_exists2__main (pf | xs1, xs2, p, null)
  prval unit_v () = pf
in
  ans
end // end of [list_exists2_fun]

implement{a1,a2} list_exists2_clo {n} {p:eff} (xs1, xs2, f) = let
  typedef clo_t = (a1, a2) -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x1: a1, x2: a2, p_f: !ptr l_f):<p> bool = !p_f (x1, x2)
  prval pf = view@ f
  val ans = list_exists2__main<a1,a2> {V} {ptr l_f} (pf | xs1, xs2, app, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_exists2_clo]

implement{a1,a2} list_exists2_cloptr {n} {p:eff} (xs1, xs2, p) = let
  viewtypedef cloptr_t = (a1, a2) -<cloptr,p> bool
  fn app (pf: !unit_v | x1: a1, x2: a2, p: !cloptr_t):<p> bool = p (x1, x2)
  prval pf = unit_v ()
  val ans = list_exists2__main<a1,a2> {unit_v} {cloptr_t} (pf | xs1, xs2, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_exists2_cloptr]

implement{a1,a2} list_exists2_cloref {n} {p:eff} (xs1, xs2, p) = let
  viewtypedef cloref_t = (a1, a2) -<cloref,p> bool
  fn app (pf: !unit_v | x1: a1, x2: a2, p: !cloref_t):<p> bool = p (x1, x2)
  prval pf = unit_v ()
  val ans = list_exists2__main<a1,a2> {unit_v} {cloref_t} (pf | xs1, xs2, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_exists2_cloref]

(* ****** ****** *)

implement{a} list_extend (xs, y) = let
  var res: List a // uninitialized
  fun loop {n:nat} .<n>.
    (xs: list (a, n), y: a, res: &(List a)? >> list (a, n+1))
    :<> void = begin case+ xs of
    | x :: xs => let
        val () = (res := cons {a} {0} (x, ?)); val cons (_, !p) = res
      in
        loop (xs, y, !p); fold@ res
      end // end of [::]
    | nil () => (res := cons (y, nil ()))
  end // end of [loop]
in
  loop (xs, y, res); res
end // end of [list_extend]

(* ****** ****** *)

implement{a} list_filter__main
  {v} {vt} {n} {p:eff} (pf | xs, p, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | xs: list (a, n)
    , p: (!v | a, !vt) -<fun,p> bool
    , res: &(List a)? >> list (a, n1)
    , env: !vt
    ) :<p> #[n1:nat | n1 <= n] void = case+ xs of
    | x :: xs => begin
        if p (pf | x, env) then let
          val () = res := cons {a} {0} (x, ?)
          val+ cons (_, !p_res) = res
        in
          loop (pf | xs, p, !p_res, env); fold@ res
        end else begin
          loop (pf | xs, p, res, env)
        end // end of [if]
      end (* end of [::] *)
    | nil () => (res := nil ())
  // end of [loop]
  var res: List a // uninitialized
  val () = loop (pf | xs, p, res, env)
in
  res
end // end of [list_filter__main]

implement{a} list_filter_fun {n} {p:eff} (xs, f) = let
  val f = coerce (f) where { extern castfn
    coerce (f: a -<p> bool):<> (!unit_v | a, !Ptr) -<p> bool
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_filter__main (pf | xs, f, null)
  prval unit_v () = pf
in
  ans
end // end of [list_filter_fun]

implement{a} list_filter_clo {n} {p:eff} (xs, f) = let
  typedef clo_t = a -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x: a, p_f: !ptr l_f):<p> bool = !p_f (x)
  prval pf = view@ f
  val ans = list_filter__main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_filter_clo]

implement{a} list_filter_cloptr {n} {p:eff} (xs, p) = let
  viewtypedef cloptr_t = a -<cloptr,p> bool
  fn app (pf: !unit_v | x: a, p: !cloptr_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_filter__main<a> {unit_v} {cloptr_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_filter_cloptr]

implement{a} list_filter_cloref {n} {p:eff} (xs, p) = let
  typedef cloref_t = a -<cloref,p> bool
  fn app (pf: !unit_v | x: a, p: !cloref_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_filter__main<a> {unit_v} {cloref_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_filter_cloref]

(* ****** ****** *)

implement{a} list_find__main {v} {vt} {p:eff} (pf | xs, p, env) = let
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

implement{a} list_find_fun {p:eff} (xs, f) = let
  val f = coerce (f) where { extern castfn
    coerce (f: a -<p> bool):<> (!unit_v | a, !Ptr) -<p> bool
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_find__main (pf | xs, f, null)
  prval unit_v () = pf
in
  ans
end // end of [list_find_fun]

implement{a} list_find_clo {p:eff} (xs, f) = let
  typedef clo_t = a -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x: a, p_f: !ptr l_f):<p> bool = !p_f (x)
  prval pf = view@ f
  val ans = list_find__main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_find_clo]

implement{a} list_find_cloptr {p:eff} (xs, p) = let
  viewtypedef cloptr_t = a -<cloptr,p> bool
  fn app (pf: !unit_v | x: a, p: !cloptr_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_find__main<a> {unit_v} {cloptr_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_find_cloptr]

implement{a} list_find_cloref {p:eff} (xs, p) = let
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

macrodef list_fold_left_mac (list_fold_left, f, res, xs) = `(
  case+ ,(xs) of
  | x :: xs => ,(list_fold_left) (,(f), ,(f) (,(res), x), xs)
  | nil () => ,(res)
)

*)

implement{sink,a} list_fold_left__main
  {v} {vt} {f:eff} (pf | f, res, xs, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | f: (!v | sink, a, !vt) -<fun,f> sink
    , res: sink
    , xs: list (a, n)
    , env: !vt
  ) :<f> sink = case+ xs of
    | x :: xs => let
        val res = f (pf | res, x, env) in loop (pf | f, res, xs, env)
      end // end of [::]
    | nil () => res
  // end of [loop]
in
  loop (pf | f, res, xs, env)
end // end of [list_fold_left__main]

implement{sink,a} list_fold_left_fun {f:eff} (f, res, xs) = let
  val f = coerce (f) where {
    extern castfn coerce (f: (sink, a) -<f> sink):<> (!unit_v | sink, a, !Ptr) -<f> sink
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_fold_left__main (pf | f, res, xs, null)
  prval unit_v () = pf
in
  ans
end // end of [list_fold_left_fun]

implement{sink,a} list_fold_left_clo {f:eff} (f, res, xs) = let
  viewtypedef clo_t = (sink, a) -<clo,f> sink
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | res: sink, x: a, p_f: !ptr l_f):<f> sink = !p_f (res, x)
  prval pf = view@ f
  val ans = list_fold_left__main<sink,a> {V} {ptr l_f} (pf | app, res, xs, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_fold_left_clo]

implement{sink,a} list_fold_left_cloptr {f:eff} (f, res, xs) = let
  viewtypedef cloptr_t = (sink, a) -<cloptr,f> sink
  fn app (pf: !unit_v | res: sink, x: a, f: !cloptr_t):<f> sink = f (res, x)
  prval pf = unit_v ()
  val ans = list_fold_left__main<sink,a> {unit_v} {cloptr_t} (pf | app, res, xs, f)
  prval unit_v () = pf
in
  ans
end // end of [list_fold_left_cloptr]

implement{sink,a} list_fold_left_cloref {f:eff} (f, res, xs) = let
  typedef cloref_t = (sink, a) -<cloref,f> sink
  fn app (pf: !unit_v | res: sink, x: a, f: !cloref_t):<f> sink = f (res, x)
  prval pf = unit_v ()
  val ans = list_fold_left__main<sink,a> {unit_v} {cloref_t} (pf | app, res, xs, f)
  prval unit_v () = pf
in
  ans
end // end of [list_fold_left_cloref]

(* ****** ****** *)

implement{sink,a1,a2} list_fold2_left__main
  {v} {vt} {n} {f:eff} (pf | f, res, xs1, xs2, env) = let
  fun loop {n:nat} .<n>. (
      pf: !v
    | f: !(!v | sink, a1, a2, !vt) -<fun,f> sink
    , res: sink
    , xs1: list (a1, n)
    , xs2: list (a2, n)
    , env: !vt
    ) :<f> sink = case+ xs1 of
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

implement{sink,a1,a2} list_fold2_left_cloptr {n} {f:eff} (f, res, xs1, xs2) = let
  viewtypedef cloptr_t = (sink, a1, a2) -<cloptr,f> sink
  fn app (pf: !unit_v | res: sink, x1: a1, x2: a2, f: !cloptr_t):<f> sink = f (res, x1, x2)
  prval pf = unit_v ()
  val ans = list_fold2_left__main<sink,a1,a2> {unit_v} {cloptr_t} (pf | app, res, xs1, xs2, f)
  prval unit_v () = pf
in
  ans
end // end of [list_fold2_left_cloptr]

implement{sink,a1,a2} list_fold2_left_cloref {n} {f:eff} (f, res, xs1, xs2) = let
  typedef cloref_t = (sink, a1, a2) -<cloref,f> sink
  fn app (pf: !unit_v | res: sink, x1: a1, x2: a2, f: !cloref_t):<f> sink = f (res, x1, x2)
  prval pf = unit_v ()
  val ans = list_fold2_left__main<sink,a1,a2> {unit_v} {cloref_t} (pf | app, res, xs1, xs2, f)
  prval unit_v () = pf
in
  ans
end // end of [list_fold2_left_cloref]

(* ****** ****** *)

implement{a,sink} list_fold_right__main
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

implement{a,sink} list_fold_right_fun {f:eff} (f, xs, res) = let
  val f = coerce (f) where {
    extern castfn coerce (f: (a, sink) -<f> sink):<> (!unit_v | a, sink, !Ptr) -<f> sink
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_fold_right__main (pf | f, xs, res, null)
  prval unit_v () = pf
in
  ans
end // end of [list_fold_right_fun]

implement{a,sink} list_fold_right_clo {f:eff} (f, xs, res) = let
  viewtypedef clo_t = (a, sink) -<clo,f> sink
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x: a, res: sink, p_f: !ptr l_f):<f> sink = !p_f (x, res)
  prval pf = view@ f
  val ans = list_fold_right__main<a,sink> {V} {ptr l_f} (pf | app, xs, res, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_fold_right_clo]

implement{a,sink} list_fold_right_cloptr {f:eff} (f, xs, res) = let
  viewtypedef cloptr_t = (a,sink) -<cloptr,f> sink
  fn app (pf: !unit_v | x: a, res: sink, f: !cloptr_t):<f> sink = f (x, res)
  prval pf = unit_v ()
  val ans = list_fold_right__main<a,sink> {unit_v} {cloptr_t} (pf | app, xs, res, f)
  prval unit_v () = pf
in
  ans
end // end of [list_fold_right_cloptr]

implement{a,sink} list_fold_right_cloref {f:eff} (f, xs, res) = let
  typedef cloref_t = (a,sink) -<cloref,f> sink
  fn app (pf: !unit_v | x: a, res: sink, f: !cloref_t):<f> sink = f (x, res)
  prval pf = unit_v ()
  val ans = list_fold_right__main<a,sink> {unit_v} {cloref_t} (pf | app, xs, res, f)
  prval unit_v () = pf
in
  ans
end // end of [list_fold_right_cloref]

(* ****** ****** *)

implement{a1,a2,sink} list_fold2_right__main
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

implement{a} list_forall__main {v} {vt} {p:eff} (pf | xs, p, env) = let
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

implement{a} list_forall_fun {p:eff} (xs, p) = let
  val p = coerce (p) where {
    extern castfn coerce (p: a -<p> bool):<> (!unit_v | a, !Ptr) -<p> bool
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_forall__main (pf | xs, p, null)
  prval unit_v () = pf
in
  ans
end // end of [list_forall_fun]

implement{a} list_forall_clo {p:eff} (xs, f) = let
  typedef clo_t = a -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x: a, p_f: !ptr l_f):<p> bool = !p_f (x)
  prval pf = view@ f
  val ans = list_forall__main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_forall_clo]

implement{a} list_forall_cloptr {p:eff} (xs, p) = let
  viewtypedef cloptr_t = a -<cloptr,p> bool
  fn app (pf: !unit_v | x: a, p: !cloptr_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_forall__main<a> {unit_v} {cloptr_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_forall_cloptr]

implement{a} list_forall_cloref {p:eff} (xs, p) = let
  typedef cloref_t = a -<cloref,p> bool
  fn app (pf: !unit_v | x: a, p: !cloref_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_forall__main<a> {unit_v} {cloref_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_forall_cloref]

(* ****** ****** *)

implement{a1,a2} list_forall2__main
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

implement{a1,a2} list_forall2_fun {n} {p:eff} (xs1, xs2, p) = let
  val p = coerce (p) where {
    extern castfn coerce (p: (a1, a2) -<p> bool):<> (!unit_v | a1, a2, !Ptr) -<p> bool
  } // end of [where]
  prval pf = unit_v ()
  val ans = list_forall2__main (pf | xs1, xs2, p, null)
  prval unit_v () = pf
in
  ans
end // end of [list_forall2_fun]

implement{a1,a2} list_forall2_clo {n} {p:eff} (xs1, xs2, f) = let
  typedef clo_t = (a1, a2) -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x1: a1, x2: a2, p_f: !ptr l_f):<p> bool = !p_f (x1, x2)
  prval pf = view@ f
  val ans = list_forall2__main<a1,a2> {V} {ptr l_f} (pf | xs1, xs2, app, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_forall2_clo]

implement{a1,a2} list_forall2_cloptr {n} {p:eff} (xs1, xs2, p) = let
  viewtypedef clo_t = (a1, a2) -<cloptr,p> bool
  fn app (pf: !unit_v | x1: a1, x2: a2, p: !clo_t):<p> bool = p (x1, x2)
  prval pf = unit_v ()
  val ans = list_forall2__main<a1,a2> {unit_v} {clo_t} (pf | xs1, xs2, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_forall2_cloptr]

implement{a1,a2} list_forall2_cloref {n} {p:eff} (xs1, xs2, p) = let
  viewtypedef clo_t = (a1, a2) -<cloref,p> bool
  fn app (pf: !unit_v | x1: a1, x2: a2, p: !clo_t):<p> bool = p (x1, x2)
  prval pf = unit_v ()
  val ans = list_forall2__main<a1,a2> {unit_v} {clo_t} (pf | xs1, xs2, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_forall2_cloref]

(* ****** ****** *)

implement{a} list_foreach__main
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

implement{a} list_foreach_fun {v} {f:eff} (pf | xs, f) = let
  val f = coerce (f) where { extern castfn
    coerce (f: (!v | a) -<f> void):<> (!v | a, !Ptr) -<f> void
  } // end of [where]
  val () = list_foreach__main (pf | xs, f, null)
in
  // empty
end // end of [list_foreach_fun]

implement{a} list_foreach_clo {v} {f:eff} (pf1 | xs, f) = let
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

implement{a} list_foreach_cloptr {f:eff} (xs, f) = let
  viewtypedef cloptr_t = (a) -<cloptr,f> void
  fn app (pf: !unit_v | x: a, f: !cloptr_t):<f> void = f (x)
  prval pf = unit_v ()
  val () = list_foreach__main<a> {unit_v} {cloptr_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  // empty
end // end of [list_foreach_cloptr]

implement{a} list_foreach_cloref {f:eff} (xs, f) = let
  typedef cloref_t = (a) -<cloref,f> void
  fn app (pf: !unit_v | x: a, f: !cloref_t):<f> void = f (x)
  prval pf = unit_v ()
  val () = list_foreach__main<a> {unit_v} {cloref_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  // empty
end // end of [list_foreach_cloref]

(* ****** ****** *)

implement{a1,a2} list_foreach2__main
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
  list_foreach2_fun {v} {n} {f} (pf | xs, ys, f) = let
  val f = coerce (f) where { extern castfn
    coerce (f: (!v | a1, a2) -<f> void):<> (!v | a1, a2, !Ptr) -<f> void
  } // end of [where]
  val () = list_foreach2__main (pf | xs, ys, f, null)
in
  // empty
end // end of [list_foreach2_fun]

implement{a1,a2} list_foreach2_clo {v} {n} {f:eff} (pf1 | xs1, xs2, f) = let
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
  list_foreach2_cloptr {n} {f:eff} (xs1, xs2, f) = let
  viewtypedef cloptr_t = (a1, a2) -<cloptr,f> void
  fn app (pf: !unit_v | x1: a1, x2: a2, f: !cloptr_t):<f> void =
    f (x1, x2)
  prval pf = unit_v ()
  val () = begin
    list_foreach2__main<a1,a2> {unit_v} {cloptr_t} (pf | xs1, xs2, app, f)
  end // end of [val]
  prval unit_v () = pf
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

implement{a} list_iforeach__main
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

implement{a} list_iforeach_fun {v} {n} {f:eff} (pf | xs, f) = let
  val f = coerce (f) where { extern castfn
    coerce (f: (!v | natLt n, a) -<f> void):<> (!v | natLt n, a, !Ptr) -<f> void
  } // end of [where]
  val () = list_iforeach__main (pf | xs, f, null)
in
  // empty
end // end of [list_iforeach_fun]

implement{a} list_iforeach_clo {v} {n} {f:eff} (pf1 | xs, f) = let
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

implement{a} list_iforeach_cloptr {n} {f:eff} (xs, f) = let
  viewtypedef cloptr_t = (natLt n, a) -<cloptr,f> void
  fn app (pf: !unit_v | i: natLt n, x: a, f: !cloptr_t):<f> void = f (i, x)
  prval pf = unit_v ()
  val () = list_iforeach__main<a> {unit_v} {cloptr_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  // empty
end // end of [list_iforeach_cloptr]

implement{a} list_iforeach_cloref {n} {f:eff} (xs, f) = let
  typedef cloref_t = (natLt n, a) -<cloref,f> void
  fn app (pf: !unit_v | i: natLt n, x: a, f: !cloref_t):<f> void = f (i, x)
  prval pf = unit_v ()
  val () = list_iforeach__main<a> {unit_v} {cloref_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  // empty
end // end of [list_iforeach_cloref]

(* ****** ****** *)

implement{a1,a2} list_iforeach2__main
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

implement{a1,a2} list_iforeach2_clo {v} {n} {f:eff} (pf1 | xs1, xs2, f) = let
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
  list_iforeach2_cloptr {n} {f:eff} (xs1, xs2, f) = let
  viewtypedef cloptr_t = (natLt n, a1, a2) -<cloptr,f> void
  fn app (pf: !unit_v | i: natLt n, x1: a1, x2: a2, f: !cloptr_t):<f> void =
    f (i, x1, x2)
  prval pf = unit_v ()
  val () = begin
    list_iforeach2__main<a1,a2> {unit_v} {cloptr_t} (pf | xs1, xs2, app, f)
  end // end of [val]
  prval unit_v () = pf
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

implement{a} list_get_elt_at (xs, i) = let
  fun loop {n,i:nat | i < n} .<n>.
    (xs: list (a, n), i: int i):<> a = let
    val x :: xs = xs
  in
    if i > 0 then loop (xs, i - 1) else x
  end // end of [loop]
in
  loop (xs, i)
end // end of [list_get_elt_at]

implement{a} list_nth (xs, i) = list_get_elt_at<a> (xs, i)

implement{a} list_get_elt_at_exn (xs, i) = let
  fun loop {n,i:nat} .<n>. 
    (xs: list (a, n), i: int i):<!exn> [n>0] a =
    case+ xs of
    | x :: xs => if i > 0 then loop (xs, i - 1) else x
    | nil () => $raise ListSubscriptException ()
  // end of [loop]
in
  loop (xs, i)
end // end of [list_get_elt_at_exn]

implement{a} list_nth_exn (xs, i) = list_get_elt_at_exn<a> (xs, i)

implement{a} list_get_elt_at_opt (xs, i) = let
  fun loop {n,i:nat} .<n>.
    (xs: list (a, n), i: int i):<> Option_vt a =
    case+ xs of
    | x :: xs => if i > 0 then loop (xs, i - 1) else Some_vt x
    | nil () => None_vt ()
  // end of [loop]
in
  loop (xs, i)
end // end of [list_get_elt_at_opt]

implement{a} list_nth_opt (xs, n) = list_get_elt_at_opt<a> (xs, n)

(* ****** ****** *)

implement{a} list_head (xs) = let val x :: _ = xs in x end
implement{a} list_head_exn (xs) = case xs of
  | x :: _ => x | nil () => $raise ListSubscriptException
// end of [list_hean_exn]

(* ****** ****** *)

implement{} list_is_empty {a} (xs) = begin
  case+ xs of cons _ => false | nil _ => true
end // end of [list_is_empty]

implement{} list_isnot_empty {a} (xs) = begin
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

implement{a} list_last_exn (xs) = case+ xs of
  | _ :: _ => list_last (xs) | nil () => begin
      $raise ListSubscriptException
    end // end of [nil]
// end of [list_last_exn]

(* ****** ****** *)

implement{a} list_length (xs) = let
  fun loop {i,j:nat} .<i>.
    (xs: list (a, i), j: int j):<> int (i+j) = begin
    case+ xs of  _ :: xs => loop (xs, isucc j) | nil () => j
  end // end of [loop]
in
  loop (xs, 0)
end // end of [list_length]

(* ****** ****** *)

implement{a} list_make_elt (x, n) = let
  fun loop {i,j:nat} .<i>.
    (i: int i, res: list (a, j)):<> list (a, i+j) =
    if i > 0 then loop (i-1, x :: res) else res
in
  loop (n, nil)
end // end of [list_make_elt]

(* ****** ****** *)

implement{a,b} list_map__main
  {v} {vt} {n} {f:eff} (pf | xs, f, env) = let
  typedef fun_t = (!v | a, !vt) -<fun,f> b
  fun loop {n:nat} .<n>. (
      pf: !v
    | xs: list (a, n)
    , f: fun_t
    , res: &(List b)? >> list (b, n)
    , env: !vt
    ) :<f> void = begin case+ xs of
    | x :: xs => let
        val y = f (pf | x, env)
        val+ () = (res := cons {b} {0} (y, ?)); val+ cons (_, !p) = res
      in
        loop (pf | xs, f, !p, env); fold@ res
      end // end of [::]
    | nil () => (res := nil ())
  end // end of [loop]
  var res: List b // uninitialized
in
  loop (pf | xs, f, res, env); res
end // end of [list_map__main]

implement{a,b} list_map_fun {n:int} {f:eff} (xs, f) = let
  val f = coerce (f) where {
    extern castfn coerce (f: a -<f> b):<> (!unit_v | a, !Ptr) -<f> b
  } // end of [where]
  prval pf = unit_v ()
  val ys = list_map__main (pf | xs, f, null)
  prval unit_v () = pf
in
  ys
end // end of [list_map_fun]

implement{a,b} list_map_clo {n:int} {f:eff} (xs, f) = let
  viewtypedef clo_t = a -<clo,f> b
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x: a, p_f: !ptr l_f):<f> b = !p_f (x)
  prval pf = view@ f
  val ys = list_map__main<a,b> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = view@ f := pf
in
  ys
end // end of [list_map_clo]

implement{a,b} list_map_cloptr {n:int} {f:eff} (xs, f) = let
  viewtypedef cloptr_t = a -<cloptr,f> b
  fn app (pf: !unit_v | x: a, f: !cloptr_t):<f> b = f (x)
  prval pf = unit_v ()
  val ys = list_map__main<a,b> {unit_v} {cloptr_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  ys
end // end of [list_map_cloptr]

implement{a,b} list_map_cloref {n:int} {f:eff} (xs, f) = let
  typedef cloref_t = a -<cloref,f> b
  fn app (pf: !unit_v | x: a, f: !cloref_t):<f> b = f (x)
  prval pf = unit_v ()
  val ys = list_map__main<a,b> {unit_v} {cloref_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  ys
end // end of [list_map_cloref]

(* ****** ****** *)

implement{a1,a2,b} list_map2__main
  {v:view} {vt:viewtype} {n} {f:eff} (pf | xs, ys, f, env) = let
  var res: List b // uninitialized
  fun loop {n:nat} .<n>. (
      pf: !v
    | xs: list (a1, n)
    , ys: list (a2, n)
    , f: (!v | a1, a2, !vt) -<fun,f> b
    , res: &(List b)? >> list (b, n)
    , env: !vt
  ) :<f> void = begin case+ (xs, ys) of
    | (x :: xs, y :: ys) => let
        val z = f (pf | x, y, env)
        val+ () = (res := cons {b} {0} (z, ?))
        val+ cons (_, !p) = res
      in
        loop (pf | xs, ys, f, !p, env); fold@ res
      end
    | (nil (), nil ()) => (res := nil ())
  end // end of [loop]
in
  loop (pf | xs, ys, f, res, env); res
end // end of [list_map2__main]

implement{a1,a2,b} list_map2_fun {n} {f:eff} (xs, ys, f) = let
  val f = coerce (f) where { extern castfn
    coerce (f: (a1, a2) -<f> b):<> (!unit_v | a1, a2, !Ptr) -<f> b
  } // end of [where]
  prval pf = unit_v ()
  val zs = list_map2__main (pf | xs, ys, f, null)
  prval unit_v () = pf
in
  zs
end // end of [list_map2_fun]

implement{a1,a2,b} list_map2_clo {n} {f:eff} (xs1, xs2, f) = let
  typedef clo_t = (a1, a2) -<clo,f> b
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x1: a1, x2: a2, p_f: !ptr l_f):<f> b = !p_f (x1, x2)
  prval pf = view@ f
  val ans = list_map2__main<a1,a2,b> {V} {ptr l_f} (pf | xs1, xs2, app, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_map2_clo]

implement{a1,a2,b} list_map2_cloptr {n} {f:eff} (xs, ys, f) = let
  viewtypedef cloptr_t = (a1, a2) -<cloptr,f> b
  fn app (pf: !unit_v | x: a1, y: a2, f: !cloptr_t):<f> b = f (x, y)
  prval pf = unit_v ()
  val zs = begin
    list_map2__main<a1,a2,b> {unit_v} {cloptr_t} (pf | xs, ys, app, f)
  end // end of [val]
  prval unit_v () = pf
in
  zs
end  // end of [list_map2_cloptr]

implement{a1,a2,b} list_map2_cloref {n} {f:eff} (xs, ys, f) = let
  typedef cloref_t = (a1, a2) -<cloref,f> b
  fn app (pf: !unit_v | x: a1, y: a2, f: !cloref_t):<f> b = f (x, y)
  prval pf = unit_v ()
  val zs = begin
    list_map2__main<a1,a2,b> {unit_v} {cloref_t} (pf | xs, ys, app, f)
  end // end of [val]
  prval unit_v () = pf
in
  zs
end  // end of [list_map2_cloref]

(* ****** ****** *)

implement{a} list_reverse_append (xs, ys) = let
  fun loop {n1,n2:nat} .<n1>.
    (xs: list (a, n1), ys: list (a, n2)):<> list (a, n1+n2) =
    case+ xs of x :: xs => loop (xs, x :: ys) | nil () => ys
in
  loop (xs, ys)
end // end of [list_reverse_append]

implement{a} list_reverse xs = list_reverse_append (xs, nil ())

(* ****** ****** *)

implement{a} list_set_elt_at (xs, i, x0) = let
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

implement{a} list_set_elt_at_exn (xs, i, x0) =
  if aux_test<a> (xs, i) then list_set_elt_at (xs, i, x0)
  else $raise ListSubscriptException

implement{a} list_set_elt_at_opt (xs, i, x0) =
  if aux_test<a> (xs, i) then Some_vt (list_set_elt_at (xs, i, x0))
  else None_vt ()

end // end of [local]

(* ****** ****** *)

implement{a} list_split_at {n,i} (xs, i) = let
  var fsts: List a // uninitialized
  fun loop {j:nat | j <= i} .<i-j>.
    (xs: list (a, n-j), ij: int (i-j), fsts: &(List a)? >> list (a, i-j))
    :<> list (a, n-i) =
    if ij > 0 then let
      val+ x :: xs = xs
      val () = (fsts := cons {a} {0} (x, ?)); val+ cons (_, !p) = fsts
      val snds = loop {j+1} (xs, ij - 1, !p)
    in
      fold@ fsts; snds
    end else begin
      fsts := nil (); xs
    end
  val snds = loop {0} (xs, i, fsts)
in
  (fsts, snds)
end // end of [list_split_at]

(* ****** ****** *)

implement{a} list_tail (xs) = let val _ :: xs = xs in xs end
implement{a} list_tail_exn (xs) = case+ xs of
  | _ :: xs => xs | nil () => $raise ListSubscriptException

(* ****** ****** *)

implement{a} list_take (xs, i) = let
  var res: List a // uninitialized
  fun loop {n,i:nat | i <= n} .<i>.
    (xs: list (a, n), i: int i, res: &(List a)? >> list (a, i)):<> void =
    if i > 0 then let
      val x :: xs = xs
      val () = (res := cons {a} {0} (x, ?))
      val+ cons (_, !p) = res
    in
      loop (xs, i-1, !p); fold@ res
    end else begin
      res := nil ()
   end
in
  loop (xs, i, res); res
end // end of [list_take]

(* ****** ****** *)

implement{a,b} list_zip (xs, ys) = let
  typedef ab = '(a, b)
  var res: List ab // uninitialized
  fun loop {i:nat} .<i>.
    (xs: list (a, i), ys: list (b, i), res: &(List ab)? >> list (ab, i)):<> void =
    case+ (xs, ys) of
    | (x :: xs, y :: ys) => let
        val () = (res := cons {ab} {0} ('(x, y), ?)); val+ cons (_, !p) = res
      in
        loop (xs, ys, !p); fold@ res
      end
    | (nil (), nil ()) => (res := nil ())
in
  loop (xs, ys, res); res
end // end of [list_zip]

(* ****** ****** *)

implement{a,b,c} list_zipwith_fun {n} {f:eff} (xs, ys, f) =
  list_map2_fun<a,b,c> (xs, ys, f)

implement{a,b,c} list_zipwith_clo {n} {f:eff} (xs, ys, f) =
  list_map2_clo<a,b,c> (xs, ys, f)

implement{a,b,c} list_zipwith_cloptr {n} {f:eff} (xs, ys, f) =
  list_map2_cloptr<a,b,c> (xs, ys, f)

implement{a,b,c} list_zipwith_cloref {n} {f:eff} (xs, ys, f) =
  list_map2_cloref<a,b,c> (xs, ys, f)

(* ****** ****** *)

implement{a1,a2} list_unzip xys = let
  var res1: List a1 and res2: List a2 // uninitialized
  fun loop {n:nat} .<n>. (
      xys: list ('(a1, a2), n)
    , res1: &(List a1)? >> list (a1, n)
    , res2: &(List a2)? >> list (a2, n)
  ) :<> void = begin case+ xys of
    | xy :: xys => let
        val () = (res1 := cons {a1} {0} (xy.0, ?)); val+ cons (_, !p1) = res1
        val () = (res2 := cons {a2} {0} (xy.1, ?)); val+ cons (_, !p2) = res2
      in
        loop (xys, !p1, !p2); fold@ res1; fold@ res2
      end
    | nil () => (res1 := nil (); res2 := nil ())
  end // end of [loop]
in
  loop (xys, res1, res2); (res1, res2)
end // end of [list_unzip]

(* ****** ****** *)


// implementing merge sort

(*
 *
 * llist(a, i, n): a list of lists such that
 *   1. the sum of the lengths of lists in the list of lists is i, and
 *   2. the length of the list is n.
 *
 *)

local

//
// this is not an efficient implementation but it is guaranteed to be O(n*log(n))
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
      end
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

implement{a} list_mergesort (xs, lte, env) = aux4 (lte, aux1 (lte, xs, env), env)

end // end of [local]

(* ****** ****** *)

// implementing quick sort

local

//
// this may not be a practical implementation as it can easily be O(n*n)
//

  typedef lte (a:t@ype, env: viewtype, f:eff) = (a, a, !env) -<fun,f> bool

  fun{a:t@ype} qs {env:viewtype} {n:nat} {f:eff} .<n,0>.
    (lte: lte (a, env, f), xs: list (a, n), env: !env)
    :<f> list (a, n) = begin
    case+ xs of // [case+]: exhaustive pattern matching
    | x' :: xs' => begin
        part {env} {n-1,0,0} (lte, x', xs', nil, nil, env)
      end // end of [::]
    | nil () => nil ()
  end // end of [qs]

  and part {env:viewtype} {p,l,r:nat} {f:eff} .<p+l+r,p+1>. (
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
        list_append (qs (lte, l, env), x :: qs (lte, r, env))
      end // end of [nil]
  end // end of [part]
in

implement{a} list_quicksort (xs, lte, env) = qs (lte, xs, env)

end // end of [local]

(* ****** ****** *)

// [list.sats] is already loaded by a call to [pervasive_load]
staload _(*anonymous*) = "prelude/SATS/list.sats" // this forces that the static
// loading function for [list.sats] is to be called at run-time
// this is really needed only if some datatypes are declared in [list.sats]

(* ****** ****** *)

(* end of [list.dats] *)
