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

//

implement{a1,a2} list_assoc_fun {eq:eff} (xys, eq, x0) = let
  fun aux {n:nat} .<n>. (xys: list ('(a1, a2), n)):<eq> Option a2 =
    case+ xys of
    | '(x, y) :: xys => if eq (x0, x) then Some (y) else aux xys
    | nil () => None ()
in
  aux xys
end // end of [list_assoc]

//

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
  fun aux {n,i:nat | i <= n} .<i>.
    (xs: list (a, n), i: int i):<> list (a, n-i) =
    if i > 0 then let val _ :: xs = xs in aux (xs, i-1) end
    else xs
in
  aux (xs, i)
end // end of [list_drop]

(* ****** ****** *)

implement{a} list_exists_main (pf | xs, p, env) = begin
  case+ xs of
  | x :: xs => begin
      if p (pf | x, env) then true
      else begin
        list_exists_main (pf | xs, p, env)
      end
    end
  | nil () => false
end // end of [list_exists_main]

implement{a} list_exists_clo {p:eff} (xs, f) = let
  typedef clo_t = a -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x: a, p_f: !ptr l_f):<p> bool = !p_f (x)
  prval pf = view@ f
  val ans = list_exists_main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_exists_clo]

implement{a} list_exists_cloptr {p:eff} (xs, p) = let
  viewtypedef cloptr_t = a -<cloptr,p> bool
  fn app (pf: !unit_v | x: a, p: !cloptr_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_exists_main<a> {unit_v} {cloptr_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_exists_cloptr]

implement{a} list_exists_cloref {p:eff} (xs, p) = let
  typedef cloref_t = a -<cloref,p> bool
  fn app (pf: !unit_v | x: a, p: !cloref_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_exists_main<a> {unit_v} {cloref_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_exists_cloref]

(* ****** ****** *)

implement{a1,a2} list_exists2_main
  (pf | xs1, xs2, p, env) = begin case+ xs1 of
  | x1 :: xs1 => let
      val+ x2 :: xs2 = xs2
    in
      if p (pf | x1, x2, env) then true
      else begin
        list_exists2_main (pf | xs1, xs2, p, env)
      end // end of [if]
    end (* end of [::] *)
  | nil () => false
end // end of [list_exists2_main]

implement{a1,a2} list_exists2_clo {n} {p:eff} (xs1, xs2, f) = let
  typedef clo_t = (a1, a2) -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x1: a1, x2: a2, p_f: !ptr l_f):<p> bool = !p_f (x1, x2)
  prval pf = view@ f
  val ans = list_exists2_main<a1,a2> {V} {ptr l_f} (pf | xs1, xs2, app, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_exists2_clo]

implement{a1,a2} list_exists2_cloptr {n} {p:eff} (xs1, xs2, p) = let
  viewtypedef cloptr_t = (a1, a2) -<cloptr,p> bool
  fn app (pf: !unit_v | x1: a1, x2: a2, p: !cloptr_t):<p> bool = p (x1, x2)
  prval pf = unit_v ()
  val ans = list_exists2_main<a1,a2> {unit_v} {cloptr_t} (pf | xs1, xs2, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_exists2_cloptr]

implement{a1,a2} list_exists2_cloref {n} {p:eff} (xs1, xs2, p) = let
  viewtypedef cloref_t = (a1, a2) -<cloref,p> bool
  fn app (pf: !unit_v | x1: a1, x2: a2, p: !cloref_t):<p> bool = p (x1, x2)
  prval pf = unit_v ()
  val ans = list_exists2_main<a1,a2> {unit_v} {cloref_t} (pf | xs1, xs2, app, p)
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

implement{a} list_filter_main {v} {vt} {n} {p:eff} (pf | xs, p, env) = let
  fun aux {n:nat} .<n>.
    (pf: !v | xs: list (a, n), p: (!v | a, !vt) -<fun,p> bool, env: !vt)
    :<p> [n':nat | n' <= n] list (a, n') = case+ xs of
    | x :: xs => begin
        if p (pf | x, env) then x :: aux (pf | xs, p, env) else aux (pf | xs, p, env)
      end // end of [::]
    | nil () => nil ()
  // end of [aux]
in
  aux (pf | xs, p, env)
end // end of [list_filter_main]

implement{a} list_filter_clo {n} {p:eff} (xs, f) = let
  typedef clo_t = a -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x: a, p_f: !ptr l_f):<p> bool = !p_f (x)
  prval pf = view@ f
  val ans = list_filter_main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_filter_clo]

implement{a} list_filter_cloptr {n} {p:eff} (xs, p) = let
  viewtypedef cloptr_t = a -<cloptr,p> bool
  fn app (pf: !unit_v | x: a, p: !cloptr_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_filter_main<a> {unit_v} {cloptr_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_filter_cloptr]

implement{a} list_filter_cloref {n} {p:eff} (xs, p) = let
  typedef cloref_t = a -<cloref,p> bool
  fn app (pf: !unit_v | x: a, p: !cloref_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_filter_main<a> {unit_v} {cloref_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_filter_cloref]

(* ****** ****** *)

implement{a} list_find_main {v} {vt} {p:eff} (pf | xs, p, env) = let
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
end // end of [list_find_cloptr]

implement{a} list_find_clo {p:eff} (xs, f) = let
  typedef clo_t = a -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x: a, p_f: !ptr l_f):<p> bool = !p_f (x)
  prval pf = view@ f
  val ans = list_find_main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_find_clo]

implement{a} list_find_cloptr {p:eff} (xs, p) = let
  viewtypedef cloptr_t = a -<cloptr,p> bool
  fn app (pf: !unit_v | x: a, p: !cloptr_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_find_main<a> {unit_v} {cloptr_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_find_cloptr]

implement{a} list_find_cloref {p:eff} (xs, p) = let
  typedef cloref_t = a -<cloref,p> bool
  fn app (pf: !unit_v | x: a, p: !cloref_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_find_main<a> {unit_v} {cloref_t} (pf | xs, app, p)
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

implement{sink,a} list_fold_left_cloptr (f, res, xs) = begin
  case+ xs of
  | x :: xs => list_fold_left_cloptr (f, f (res, x), xs) | nil () => res
end // end of [list_fold_left_cloptr]

implement{sink,a1,a2}
  list_fold2_left_cloptr (f, res, xs1, xs2) = begin
  case+ xs1 of
  | x1 :: xs1 => let
      val+ x2 :: xs2 = xs2; val res = f (res, x1, x2)
    in
      list_fold2_left_cloptr (f, res, xs1, xs2)
    end
  | nil () => res
end // end of [list_fold2_left_cloptr]

(* ****** ****** *)

implement{a,sink} list_fold_right_cloptr (f, xs, res) = begin
  case+ xs of
  | x :: xs => begin
      let val res = list_fold_right_cloptr (f, xs, res) in f (x, res) end
    end // end of [::]
  | nil () => res
end // end of [list_fold_right_cloptr]

implement{a1,a2,sink} list_fold2_right_cloptr (f, xs1, xs2, res) = begin
  case+ xs1 of
  | x1 :: xs1 => let
      val+ x2 :: xs2 = xs2
      val res = list_fold2_right_cloptr (f, xs1, xs2, res)
    in
      f (x1, x2, res)
    end // end of [::]
  | nil () => res
end // end of [list_fold2_right_cloptr]

(* ****** ****** *)

implement{a} list_forall_main (pf | xs, p, env) = begin
  case+ xs of
  | x :: xs => begin
      if p (pf | x, env) then list_forall_main (pf | xs, p, env)
      else false
    end // end of [::]
  | nil () => false
end // end of [list_forall_main]

implement{a} list_forall_clo {p:eff} (xs, f) = let
  typedef clo_t = a -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x: a, p_f: !ptr l_f):<p> bool = !p_f (x)
  prval pf = view@ f
  val ans = list_forall_main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_forall_clo]

implement{a} list_forall_cloptr {p:eff} (xs, p) = let
  viewtypedef cloptr_t = a -<cloptr,p> bool
  fn app (pf: !unit_v | x: a, p: !cloptr_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_forall_main<a> {unit_v} {cloptr_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_forall_cloptr]

implement{a} list_forall_cloref {p:eff} (xs, p) = let
  typedef cloref_t = a -<cloref,p> bool
  fn app (pf: !unit_v | x: a, p: !cloref_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_forall_main<a> {unit_v} {cloref_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_forall_cloref]

(* ****** ****** *)

implement{a1,a2} list_forall2_main
  (pf | xs1, xs2, p, env) = begin case+ xs1 of
  | x1 :: xs1 => let
      val+ x2 :: xs2 = xs2
    in
      if p (pf | x1, x2, env) then
        list_forall2_main (pf | xs1, xs2, p, env)
      else false
    end
  | nil () => false
end // end of [list_forall2_main]

implement{a1,a2} list_forall2_clo {n} {p:eff} (xs1, xs2, f) = let
  typedef clo_t = (a1, a2) -<clo,p> bool
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = clo_t @ l_f
  fn app (pf: !V | x1: a1, x2: a2, p_f: !ptr l_f):<p> bool = !p_f (x1, x2)
  prval pf = view@ f
  val ans = list_forall2_main<a1,a2> {V} {ptr l_f} (pf | xs1, xs2, app, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_forall2_clo]

implement{a1,a2} list_forall2_cloptr {n} {p:eff} (xs1, xs2, p) = let
  viewtypedef clo_t = (a1, a2) -<cloptr,p> bool
  fn app (pf: !unit_v | x1: a1, x2: a2, p: !clo_t):<p> bool = p (x1, x2)
  prval pf = unit_v ()
  val ans = list_forall2_main<a1,a2> {unit_v} {clo_t} (pf | xs1, xs2, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_forall2_cloptr]

implement{a1,a2} list_forall2_cloref {n} {p:eff} (xs1, xs2, p) = let
  viewtypedef clo_t = (a1, a2) -<cloref,p> bool
  fn app (pf: !unit_v | x1: a1, x2: a2, p: !clo_t):<p> bool = p (x1, x2)
  prval pf = unit_v ()
  val ans = list_forall2_main<a1,a2> {unit_v} {clo_t} (pf | xs1, xs2, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_forall2_cloref]

(* ****** ****** *)

implement{a} list_foreach_main (pf | xs, f, env) = begin
  case+ xs of
  | x :: xs => begin
      f (pf | x, env); list_foreach_main<a> (pf | xs, f, env)
    end
  | nil () => ()
end // end of [list_foreach]

implement{a} list_foreach_fun {v} {f:eff} (pf | xs, f) = let
  val f = coerce (f) where {
    extern fun coerce (f: (!v | a) -<f> void):<> (!v | a, !Ptr) -<f> void
      = "atspre_fun_coerce"
  } // end of [where]
  val () = list_foreach_main (pf | xs, f, null)
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
  val ans = list_foreach_main<a> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = pf1 := pf.0 and () = view@ f := pf.1
in
  ans
end // end of [list_foreach_clo]

implement{a} list_foreach_cloptr {v} {f:eff} (pf | xs, f) = let
  viewtypedef cloptr_t = (!v | a) -<cloptr,f> void
  fn app (pf: !v | x: a, f: !cloptr_t):<f> void = f (pf | x)
  val () = list_foreach_main<a> {v} {cloptr_t} (pf | xs, app, f)
in
  // empty
end // end of [list_foreach_cloptr]

implement{a} list_foreach_cloref {v} {f:eff} (pf | xs, f) = let
  typedef cloref_t = (!v | a) -<cloref,f> void
  fn app (pf: !v | x: a, f: !cloref_t):<f> void = f (pf | x)
  val () = list_foreach_main<a> {v} {cloref_t} (pf | xs, app, f)
in
  // empty
end // end of [list_foreach_cloref]

(* ****** ****** *)

implement{a1,a2} list_foreach2_main (pf | xs1, xs2, f, env) = begin
  case+ xs1 of
  | x1 :: xs1 => let
      val x2 :: xs2 = xs2
    in
      f (pf | x1, x2, env); list_foreach2_main (pf | xs1, xs2, f, env)
    end
  | nil () => ()
end // end of [list_foreach2_main]

implement{a1,a2}
  list_foreach2_fun {v} {n} {f} (pf | xs, ys, f) = let
  val f = coerce (f) where {
    extern fun coerce (f: (!v | a1, a2) -<f> void)
      :<> (!v | a1, a2, !Ptr) -<f> void = "atspre_fun_coerce"
  } // end of [where]
  val () = list_foreach2_main (pf | xs, ys, f, null)
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
  val ans = list_foreach2_main<a1,a2> {V} {ptr l_f} (pf | xs1, xs2, app, p_f)
  prval () = pf1 := pf.0 and () = view@ f := pf.1
in
  ans
end // end of [list_foreach2_clo]

implement{a1,a2}
  list_foreach2_cloptr {v} {n} {f:eff} (pf | xs1, xs2, f) = let
  viewtypedef cloptr_t = (!v | a1, a2) -<cloptr,f> void
  fn app (pf: !v | x1: a1, x2: a2, f: !cloptr_t):<f> void =
    f (pf | x1, x2)
  val () = begin
    list_foreach2_main<a1,a2> {v} {cloptr_t} (pf | xs1, xs2, app, f)
  end // end of [val]
in
  // empty
end // end of [list_foreach2_cloptr]

(* ****** ****** *)

implement{a} list_iforeach_cloptr {v} {n} {f:eff} (pf | xs, f) = let
  viewtypedef cloptr_t = (!v | natLt n, a) -<cloptr,f> void
  fun aux {i,j:nat | i+j==n} .<j>.
    (pf: !v | i: int i, xs: list (a, j), f: !cloptr_t) :<f> void = begin
    case+ xs of x :: xs => (f (pf | i, x); aux (pf | i+1, xs, f)) | nil () => ()
  end // end of [aux]
in
  aux (pf | 0, xs, f)
end // end of [list_iforeach]

implement{a} list_iforeach_cloref {v} {n} {f:eff} (pf | xs, f) = let
  typedef cloref_type = (!v | natLt n, a) -<cloref,f> void
  viewtypedef cloptr_type = (!v | natLt n, a) -<cloptr,f> void
  val f = cloref_cloptr_make (f) where {
    extern castfn cloref_cloptr_make (f: cloref_type):<> cloptr_type
  } // end of [where]
  val () = list_iforeach_cloptr<a> {v} {n} {f} (pf | xs, f)
  val () = cloref_cloptr_free (f) where {
    extern castfn cloref_cloptr_free (f: cloptr_type):<> void
  } // end of [where]
in
  // empty
end // end of [list_iforeach_cloref]

(* ****** ****** *)

implement{a1,a2} list_iforeach2_cloptr
  {v} {n} {f:eff} (pf | xs1, xs2, f) = let
  viewtypedef cloptr_t = (!v | natLt n, a1, a2) -<cloptr,f> void
  fun aux {i,j:nat | i+j==n} .<j>.
    (pf: !v | i: int i, xs1: list (a1, j), xs2: list (a2, j), f: !cloptr_t)
    :<f> void = begin case+ (xs1, xs2) of
    | (x1 :: xs1, x2 :: xs2) => (f (pf | i, x1, x2); aux (pf | i+1, xs1, xs2, f))
    | (nil (), nil ()) => ()
  end // end of [aux]
in
  aux (pf | 0, xs1, xs2, f)
end // end of [list_iforeach2_cloptr]

implement{a1,a2}
  list_iforeach2_cloref {v} {n} {f:eff} (pf | xs1, xs2, f) = let
  typedef cloref_type = (!v | natLt n, a1, a2) -<cloref,f> void
  viewtypedef cloptr_type = (!v | natLt n, a1, a2) -<cloptr,f> void
  val f = cloref_cloptr_make (f) where {
    extern castfn cloref_cloptr_make (f: cloref_type):<> cloptr_type
  } // end of [where]
  val () = list_iforeach2_cloptr<a1,a2> {v} {n} {f} (pf | xs1, xs2, f)
  val () = cloref_cloptr_free (f) where {
    extern castfn cloref_cloptr_free (f: cloptr_type):<> void
  } // end of [where]
in
  // empty
end // end of [list_iforeach2_cloref]

(* ****** ****** *)

implement{a} list_get_elt_at (xs, n) = let
  fun aux {n,i:nat | i < n} .<n>.
    (xs: list (a, n), i: int i):<> a = let
    val x :: xs = xs
  in
    if i > 0 then aux (xs, pred i) else x
  end // end of [aux]
in
  aux (xs, 0)
end // end of [list_get_elt_at]

implement{a} list_nth (xs, n) = list_get_elt_at<a> (xs, n)

implement{a} list_get_elt_at_exn (xs, n) = let
  fun aux {n,i:nat} .<n>. 
    (xs: list (a, n), i: int i):<!exn> [n>0] a = begin
    case+ xs of
    | x :: xs => if i > 0 then aux (xs, pred i) else x
    | nil () => $raise ListSubscriptException ()
  end // end of [aux]
in
  aux (xs, 0)
end // end of [list_get_elt_at_exn]

implement{a} list_nth_exn (xs, n) = list_get_elt_at_exn<a> (xs, n)

implement{a} list_get_elt_at_opt (xs, n) = let
  fun aux {n,i:nat} .<n>.
    (xs: list (a, n), i: int i):<> Option_vt a = begin
    case+ xs of
    | x :: xs => if i > 0 then aux (xs, pred i) else Some_vt x
    | nil () => None_vt ()
  end // end of [aux]
in
  aux (xs, 0)
end // end of [list_get_elt_at_opt]

implement{a} list_nth_opt (xs, n) = list_get_elt_at_opt<a> (xs, n)

(* ****** ****** *)

implement{a} list_head (xs) = let val x :: _ = xs in x end
implement{a} list_head_exn (xs) = case xs of
  | x :: _ => x
  | nil () => $raise ListSubscriptException

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
  fun aux {i,j:nat} .<i>.
    (xs: list (a, i), j: int j):<> int (i+j) = begin
    case+ xs of  _ :: xs => aux (xs, isucc j) | nil () => j
  end // end of [aux]
in
  aux (xs, 0)
end // end of [list_length]

(* ****** ****** *)

implement{a} list_make_elt (x, n) = let
  fun aux {i,j:nat} .<i>.
    (i: int i, res: list (a, j)):<> list (a, i+j) =
    if i > 0 then aux (i-1, x :: res) else res
in
  aux (n, nil)
end // end of [list_make_elt]

(* ****** ****** *)

implement{a,b} list_map_main
  {v} {vt} {n} {f:eff} (pf | xs, f, env) = let
  typedef fun_t = (!v | a, !vt) -<fun,f> b
  fun aux {n:nat} .<n>. (
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
        aux (pf | xs, f, !p, env); fold@ res
      end
    | nil () => (res := nil ())
  end // end of [aux]
  var res: List b // uninitialized
in
  aux (pf | xs, f, res, env); res
end // end of [list_map_main]

implement{a,b} list_map_fun {n:int} {f:eff} (xs, f) = let
  val f = coerce (f) where {
    extern fun coerce (f: a -<f> b):<> (!unit_v | a, !Ptr) -<f> b
      = "atspre_fun_coerce"
  } // end of [where]
  prval pf = unit_v ()
  val ys = list_map_main (pf | xs, f, null)
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
  val ys = list_map_main<a,b> {V} {ptr l_f} (pf | xs, app, p_f)
  prval () = view@ f := pf
in
  ys
end // end of [list_map_clo]

implement{a,b} list_map_cloptr {n:int} {f:eff} (xs, f) = let
  viewtypedef cloptr_t = a -<cloptr,f> b
  fn app (pf: !unit_v | x: a, f: !cloptr_t):<f> b = f (x)
  prval pf = unit_v ()
  val ys = list_map_main<a,b> {unit_v} {cloptr_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  ys
end // end of [list_map_cloptr]

implement{a,b} list_map_cloref {n:int} {f:eff} (xs, f) = let
  typedef clo_type = a -<clo1> b
  val ys = $effmask_ref let
    val (vbox pf_f | p_f) = cloref_get_view_ptr {clo_type} (f)
  in
    $effmask_all (list_map_clo (xs, !p_f))
  end // end of [val]
in
  ys
end // end of [list_map_cloref]

(* ****** ****** *)

implement{a1,a2,b} list_map2_main
  {v:view} {vt:viewtype} {n} {f:eff} (pf | xs, ys, f, env) = let
  var res: List b // uninitialized
  fun aux {n:nat} .<n>. (
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
        aux (pf | xs, ys, f, !p, env); fold@ res
      end
    | (nil (), nil ()) => (res := nil ())
  end // end of [aux]
in
  aux (pf | xs, ys, f, res, env); res
end // end of [list_map2_main]

implement{a1,a2,b} list_map2_fun {n} {f:eff} (xs, ys, f) = let
  val f = coerce (f) where {
    extern fun coerce
      (f: (a1, a2) -<f> b):<> (!unit_v | a1, a2, !Ptr) -<f> b
      = "atspre_fun_coerce"
  } // end of [where]
  prval pf = unit_v ()
  val zs = list_map2_main (pf | xs, ys, f, null)
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
  val ans = list_map2_main<a1,a2,b> {V} {ptr l_f} (pf | xs1, xs2, app, p_f)
  prval () = view@ f := pf
in
  ans
end // end of [list_map2_clo]

implement{a1,a2,b} list_map2_cloptr {n} {f:eff} (xs, ys, f) = let
  viewtypedef cloptr_t = (a1, a2) -<cloptr,f> b
  fn app (pf: !unit_v | x: a1, y: a2, f: !cloptr_t):<f> b = f (x, y)
  prval pf = unit_v ()
  val zs = begin
    list_map2_main<a1,a2,b> {unit_v} {cloptr_t} (pf | xs, ys, app, f)
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
    list_map2_main<a1,a2,b> {unit_v} {cloref_t} (pf | xs, ys, app, f)
  end // end of [val]
  prval unit_v () = pf
in
  zs
end  // end of [list_map2_cloref]

(* ****** ****** *)

implement{a} list_reverse_append (xs, ys) = let
  fun aux {n1,n2:nat} .<n1>.
    (xs: list (a, n1), ys: list (a, n2)):<> list (a, n1+n2) =
    case+ xs of x :: xs => aux (xs, x :: ys) | nil () => ys
in
  aux (xs, ys)
end // end of [list_reverse_append]

implement{a} list_reverse xs = list_reverse_append (xs, nil ())

(* ****** ****** *)

implement{a} list_set_elt_at (xs, i, x0) = let
  var res: List a // uninitialized
  fun aux {n,i:nat | i < n} .<n>.
    (xs: list (a, n), i: int i, x0: a, res: &(List a)? >> list (a, n))
    :<> void = let
    val x :: xs = xs in
    if i > 0 then let
      val () = (res := cons {a} {0} (x, ?))
      val+ cons (_, !p) = res
    in
      aux (xs, i-1, x0, !p); fold@ res
    end else begin
      res := cons (x0, xs)
    end
  end // end of [aux]
in
  aux (xs, i, x0, res); res
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
  fun aux {j:nat | j <= i} .<i-j>.
    (xs: list (a, n-j), ij: int (i-j), fsts: &(List a)? >> list (a, i-j))
    :<> list (a, n-i) =
    if ij > 0 then let
      val+ x :: xs = xs
      val () = (fsts := cons {a} {0} (x, ?)); val+ cons (_, !p) = fsts
      val snds = aux {j+1} (xs, ij - 1, !p)
    in
      fold@ fsts; snds
    end else begin
      fsts := nil (); xs
    end
  val snds = aux {0} (xs, i, fsts)
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
  fun aux {n,i:nat | i <= n} .<i>.
    (xs: list (a, n), i: int i, res: &(List a)? >> list (a, i)):<> void =
    if i > 0 then let
      val x :: xs = xs
      val () = (res := cons {a} {0} (x, ?))
      val+ cons (_, !p) = res
    in
      aux (xs, i-1, !p); fold@ res
    end else begin
      res := nil ()
   end
in
  aux (xs, i, res); res
end // end of [list_take]

(* ****** ****** *)

implement{a} list_tabulate {n} {f} (f, n) = let
  var res: List a // uninitialized
  fun aux {i:nat | i <= n} .<n-i>.
    (i: int i, f: !natLt n -<f> a, res: &(List a)? >> list (a, n-i)):<f> void =
    if i < n then let
      val () = (res := cons {a} {0} (f i, ?)); val+ cons (_, !p) = res
    in
      aux (i+1, f, !p); fold@ res
    end else begin
      res := nil ()
    end
in
  aux (0, f, res); res
end // end of [list_tabulate]

(* ****** ****** *)

implement{a,b} list_zip (xs, ys) = let
  typedef ab = '(a, b)
  var res: List ab // uninitialized
  fun aux {i:nat} .<i>.
    (xs: list (a, i), ys: list (b, i), res: &(List ab)? >> list (ab, i)):<> void =
    case+ (xs, ys) of
    | (x :: xs, y :: ys) => let
        val () = (res := cons {ab} {0} ('(x, y), ?)); val+ cons (_, !p) = res
      in
        aux (xs, ys, !p); fold@ res
      end
    | (nil (), nil ()) => (res := nil ())
in
  aux (xs, ys, res); res
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
  fun aux {n:nat} .<n>. (
      xys: list ('(a1, a2), n)
    , res1: &(List a1)? >> list (a1, n)
    , res2: &(List a2)? >> list (a2, n)
  ) :<> void = begin case+ xys of
    | xy :: xys => let
        val () = (res1 := cons {a1} {0} (xy.0, ?)); val+ cons (_, !p1) = res1
        val () = (res2 := cons {a2} {0} (xy.1, ?)); val+ cons (_, !p2) = res2
      in
        aux (xys, !p1, !p2); fold@ res1; fold@ res2
      end
    | nil () => (res1 := nil (); res2 := nil ())
  end // end of [aux]
in
  aux (xys, res1, res2); (res1, res2)
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
// this is not an efficient implementation but it is guaranteed to be O(n*lg(n))
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
    | l as '[x] => lcons (l, lnil ())
    | nil () => lnil

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

  fun{a:t@ype} aux3
    {env:viewtype} {i,n:nat} {f:eff} .<n>.
    (lte: lte (a, env, f), xss: llist (a, i, n), env: !env)
    :<f> [n1:nat | (n < 2 && n1 == n) || n1 < n] llist (a, i, n1) =
    case+ xss of
    | lcons (xs1, lcons (xs2, xss)) => begin
        lcons (aux2 (lte, xs1, xs2, env), aux3 (lte, xss, env))
      end
    | _ =>> xss

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

in

implement{a} list_mergesort (xs, lte, env) = aux4 (lte, aux1 (lte, xs, env), env)

end // end of [local]

(* ****** ****** *)

// implementing quick sort

local

//
// this may not be a practicalimplementation as it can easily be O(n*n)
//

  typedef lte (a:t@ype, env: viewtype, f:eff) = (a, a, !env) -<fun,f> bool

  fun{a:t@ype} qs {env:viewtype} {n:nat} {f:eff} .<n,0>.
    (lte: lte (a, env, f), xs: list (a, n), env: !env)
    :<f> list (a, n) = begin
    case+ xs of // [case+]: exhaustive pattern matching
    | x' :: xs' => begin
        part {env} {n-1,0,0} (lte, x', xs', nil, nil, env)
      end
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
        end
      end // end of [::]
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
