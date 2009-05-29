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

#include "prelude/params.hats"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [array.sats] starts!\n"

#endif

(* ****** ****** *)

fun{a:t@ype} array_ptr_get_elt_at
  {n:nat} {i:nat | i < n} (A: &(@[a][n]), i: size_t i):<> a

fun{a:t@ype} array_ptr_set_elt_at
  {n:nat} {i:nat | i < n} (A: &(@[a][n]), i: size_t i, x: a):<> void

overload [] with array_ptr_get_elt_at
overload [] with array_ptr_set_elt_at

fun{a:viewt@ype} array_ptr_xch_elt_at
  {n,i:nat | i < n} {l:addr} (A: &(@[a][n]), i: size_t i, x: &a):<> void

(* ****** ****** *)

//
// these functions are present mostly for convenience as a programmer
// ofter uses values of the type int as array indices:
//

fun{a:t@ype} array_ptr_get_elt_at__intsz
  {n:nat} {i:nat | i < n} (A: &(@[a][n]), i: int i):<> a

fun{a:t@ype} array_ptr_set_elt_at__intsz
  {n:nat} {i:nat | i < n} (A: &(@[a][n]), i: int i, x:a):<> void

overload [] with array_ptr_get_elt_at__intsz
overload [] with array_ptr_set_elt_at__intsz

fun{a:viewt@ype} array_ptr_xch_elt_at__intsz
  {n,i:nat | i < n} {l:addr} (A: &(@[a][n]), i: int i, x: &a):<> void

(* ****** ****** *)

(*

dataview array_v (a:viewt@ype+, int, addr) =
  | {n:int | n >= 0} {l:addr}
      array_v_cons (a, n+1, l) of (a @ l, array_v (a, n, l+sizeof a))
  | {l:addr} array_v_nil (a, 0, l)
// end of [array_v]

*)

viewdef array_v (a:viewt@ype, n:int, l: addr) = @[a][n] @ l

praxi array_v_nil :
  {a:viewt@ype} {l:addr} () -<prf> array_v (a, 0, l)

praxi array_v_unnil :
  {a:viewt@ype} {l:addr} array_v (a, 0, l) -<prf> void

praxi array_v_cons : {a:viewt@ype} {n:nat} {l:addr}
  (a @ l, array_v (a, n, l+sizeof a)) -<prf> array_v (a, n+1, l)

praxi array_v_uncons : {a:viewt@ype} {n:int | n > 0} {l:addr}
  array_v (a, n, l) -<prf> (a @ l, array_v (a, n-1, l+sizeof a))

(* ****** ****** *)

praxi free_gc_viewt0ype_addr_trans
  {a1,a2:viewt@ype | sizeof a1 == sizeof a2}
  {n1,n2:int} {l:addr} {asz:int} (
    pf1_mul: MUL (n1, sizeof a1, asz)
  , pf2_mul: MUL (n2, sizeof a2, asz) 
  , pf_gc: !free_gc_v (a1, n1, l) >> free_gc_v (a2, n2, l)
  ) : void
// end of [praxi]

(* ****** ****** *)

fun{a:viewt@ype}
  array_ptr_alloc {n:nat} (asz: size_t n):<>
    [l:addr | l <> null] (free_gc_v (a, n, l), array_v (a?, n, l) | ptr l)

fun array_ptr_alloc_tsz
  {a:viewt@ype} {n:nat} (asz: size_t n, tsz: sizeof_t a):<>
    [l:addr | l <> null] (free_gc_v (a, n, l), array_v (a?, n, l) | ptr l)
  = "atspre_array_ptr_alloc_tsz"

(* ****** ****** *)

fun array_ptr_free {a:viewt@ype} {n:int} {l:addr}
  (pf_gc: free_gc_v (a, n, l), pf_arr: array_v (a?, n, l) | p_arr: ptr l):<> void
  = "atspre_array_ptr_free" 

(* ****** ****** *)

fun{a:t@ype} array_ptr_initialize_elt {n:nat}
  (base: &(@[a?][n]) >> @[a][n], asz: size_t n, ini: a):<> void

fun array_ptr_initialize_elt_tsz {a:t@ype} {n:nat}
  (base: &(@[a?][n]) >> @[a][n], asz: size_t n, ini: &a, tsz: sizeof_t a):<> void
  = "atspre_array_ptr_initialize_elt_tsz"

(* ****** ****** *)

fun{a:t@ype} array_ptr_initialize_lst {n:nat}
  (base: &(@[a?][n]) >> @[a][n], asz: size_t n, xs: list (a, n)):<> void

// the linear list is freed along the way
fun{a:viewt@ype} array_ptr_initialize_lst_vt {n:nat}
  (base: &(@[a?][n]) >> @[a][n], asz: size_t n, xs: list_vt (a, n)):<> void

(* ****** ****** *)

// implemented in [prelude/DATS/array.dats]
fun array_ptr_initialize_fun_tsz__main
  {a:viewt@ype} {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | base: &(@[a?][n]) >> @[a][n]
  , asz: size_t n
  , f: (!v | &(a?) >> a, sizeLt n, !vt) -<f> void
  , tsz: sizeof_t a
  , env: !vt
  ) :<f> void
  = "atspre_array_ptr_initialize_fun_tsz__main"

// implemented in [prelude/DATS/array.dats]
fun array_ptr_initialize_fun_tsz
  {a:viewt@ype} {n:nat} {f:eff} (
    base: &(@[a?][n]) >> @[a][n]
  , asz: size_t n
  , f: (&(a?) >> a, sizeLt n) -<f> void
  , tsz: sizeof_t a
  ) :<f> void
  = "atspre_array_ptr_initialize_fun_tsz"

(* ****** ****** *)

// implemented in [prelude/DATS/array.dats]
fun array_ptr_initialize_clo_tsz__main
  {a:viewt@ype} {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | base: &(@[a?][n]) >> @[a][n]
  , asz: size_t n
  , f: &(!v | &(a?) >> a, sizeLt n, !vt) -<clo,f> void
  , tsz: sizeof_t a
  , env: !vt
  ) :<f> void
  = "atspre_array_ptr_initialize_clo_tsz__main"

// implemented in [prelude/DATS/array.dats]
fun array_ptr_initialize_clo_tsz {a:viewt@ype} {n:nat} {f:eff} (
    base: &(@[a?][n]) >> @[a][n]
  , asz: size_t n
  , f: &(&(a?) >> a, sizeLt n) -<clo,f> void
  , tsz: sizeof_t a
  ) :<f> void
  = "atspre_array_ptr_initialize_clo_tsz"

(* ****** ****** *)

// implemented in [prelude/DATS/array.dats]
fun array_ptr_clear_clo_tsz {a:viewt@ype} {n:nat} {f:eff} (
    base: &(@[a][n]) >> @[a?][n]
  , asz: size_t n
  , f: &(&a >> a?) -<clo,f> void
  , tsz: sizeof_t (a)
  ) :<f> void
  = "atspre_array_ptr_clear_clo_tsz"

(* ****** ****** *)

prfun array_v_split {a:viewt@ype}
  {n,i:nat | i <= n} {l:addr} {ofs:int}
  (pf_mul: MUL (i, sizeof a, ofs), pf_arr: array_v (a, n, l))
  :<prf> @(array_v (a, i, l), array_v (a, n-i, l+ofs))

(* ***** ***** *)

prfun array_v_unsplit
  {a:viewt@ype} {n1,n2:nat} {l:addr} {ofs:int} (
    pf_mul: MUL (n1, sizeof a, ofs)
  , pf1_arr: array_v (a, n1, l), pf2_arr: array_v (a, n2, l+ofs)
  ) :<prf> array_v (a, n1+n2, l)

(* ***** ***** *)

prfun array_v_extend :
  {a:viewt@ype} {n:nat} {l:addr} {ofs:int}
    (MUL (n, sizeof a, ofs), array_v (a, n, l), a @ l+ofs) -<prf>
    array_v (a, n+1, l)

prfun array_v_unextend :
  {a:viewt@ype} {n:int | n > 0} {l:addr} {ofs:int}
    (MUL (n, sizeof a, ofs), array_v (a, n, l)) -<prf>
    (array_v (a, n-1, l), a @ l+ofs-sizeof a)

prfun array_v_takeout :
  {a:viewt@ype} {n,i:nat | i < n} {l:addr} {ofs:int}
    (MUL (i, sizeof a, ofs), array_v (a, n, l)) -<prf>
    (a @ l+ofs, a @ l+ofs -<lin> array_v (a, n, l))

prfun array_v_takeout2 :
  {a:viewt@ype} {n,i1,i2:nat | i1 < n; i2 < n; i1 <> i2} {l:addr} {ofs1,ofs2:int}
    (MUL (i1, sizeof a, ofs1), MUL (i2, sizeof a, ofs2), array_v (a, n, l)) -<prf>
    (a @ l+ofs1, a @ l+ofs2, (a @ l+ofs1, a @ l+ofs2) -<lin> array_v (a, n, l))

(* ***** ***** *)

prfun array_v_clear :
  {a:t@ype} {n:nat} {l:addr} array_v (a, n, l) -<prf> array_v (a?, n, l)

(* ***** ***** *)

prfun array_v_group : {a:viewt@ype} {m,n:nat} {l:addr} {mn:int}
  (MUL (m, n, mn) | array_v (a, mn, l)) -<prf> array_v (@[a][n], m, l)

prfun array_v_ungroup : {a:viewt@ype} {m,n:nat} {l:addr} {mn:int}
  (MUL (m, n, mn) | array_v (@[a][n], m, l)) -<prf> array_v (a, mn, l)

(* ****** ****** *)

fun{a:viewt@ype}
  array_ptr_takeout {n,i:nat | i < n} {l0:addr} (
    pf: array_v (a, n, l0) | base: ptr l0, offset: size_t i
  ) :<> [l:addr] (
      a @ l
    , a @ l -<lin,prf> array_v (a, n, l0)
    | ptr l
    )
// end of [array_ptr_takeout]

fun array_ptr_takeout_tsz
  {a:viewt@ype} {n,i:nat | i < n} {l0:addr} (
    pf: array_v (a, n, l0)
  | base: ptr l0, offset: size_t i, tsz: sizeof_t a
  ) :<> [l:addr] (
      a @ l
    , a @ l -<lin,prf> array_v (a, n, l0)
    | ptr l
    )
  = "atspre_array_ptr_takeout_tsz"

(* ****** ****** *)

fun{a:viewt@ype} array_ptr_takeout2
  {n,i1,i2:nat | i1 < n; i2 < n; i1 <> i2} {l0:addr} (
    pf: array_v (a, n, l0)
  | base: ptr l0
  , off1: size_t i1, off2: size_t i2
  ) :<> [l1,l2:addr] (
      a @ l1
    , a @ l2, (a @ l1, a @ l2) -<lin,prf> array_v (a, n, l0)
    | ptr l1
    , ptr l2
    )
// end of [array_ptr_takeout2]

fun array_ptr_takeout2_tsz
  {a:viewt@ype} {n,i1,i2:nat | i1 < n; i2 < n; i1 <> i2} {l0:addr} (
    pf: array_v (a, n, l0)
  | base: ptr l0
  , off1: size_t i1, off2: size_t i2
  , tsz: sizeof_t a
  ) :<> [l1,l2:addr] (
      a @ l1
    , a @ l2, (a @ l1, a @ l2) -<lin,prf> array_v (a, n, l0)
    | ptr l1
    , ptr l2
    )
  = "atspre_array_ptr_takeout2_tsz"

(* ****** ****** *)

fun array_ptr_copy_tsz {a:t@ype} {n:nat} (
    A: &(@[a][n])
  , B: &(@[a?][n]) >> @[a][n]
  , n: size_t n
  , tsz: sizeof_t a
  ) :<> void
  = "atspre_array_ptr_copy_tsz"

fun array_ptr_move_tsz {a:viewt@ype} {n:nat} (
    A: &(@[a][n]) >> @[a?][n]
  , B: &(@[a?][n]) >> @[a][n]
  , n: size_t n
  , tsz: sizeof_t a
  ) :<> void
  = "atspre_array_ptr_move_tsz"

//

fun{a:viewt@ype} array_ptr_exch
  {n,i1,i2:nat | i1 < n; i2 < n; i1 <> i2}
  (A: &(@[a][n]), i1: size_t i1, i2: size_t i2):<> void

(* ****** ****** *)

//
// these functions are just as easy to be implemented on the spot (HX)
//

// implemented in [prelude/DATS/array.dats]
fun array_ptr_foreach_fun_tsz__main
  {a:viewt@ype} {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | f: (!v | &a, !vt) -<f> void
  , base: &(@[a][n])
  , asz: size_t n
  , tsz: sizeof_t a
  , env: !vt
  ) :<f> void
  = "atspre_array_ptr_foreach_fun_tsz__main"

fun array_ptr_foreach_clo_tsz
  {a:viewt@ype} {v:view} {n:nat} {f:eff} (
    pf: !v
  | f: &(!v | &a) -<clo,f> void
  , base: &(@[a][n])
  , asz: size_t n
  , tsz: sizeof_t a
  ) :<f> void

(* ****** ****** *)

//
// these functions are just as easy to be implemented on the spot (HX)
//

// implemented in [prelude/DATS/array.dats]
fun array_ptr_iforeach_fun_tsz__main
  {a:viewt@ype} {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | f: (!v | sizeLt n, &a, !vt) -<f> void
  , base: &(@[a][n])
  , asz: size_t n
  , tsz: sizeof_t a
  , env: !vt
  ) :<f> void
  = "atspre_array_ptr_iforeach_fun_tsz__main"

fun array_ptr_iforeach_clo_tsz
  {a:viewt@ype} {v:view} {n:nat} {f:eff} (
    pf: !v
  | f: &(!v | sizeLt n, &a) -<clo,f> void
  , base: &(@[a][n])
  , asz: size_t n
  , tsz: sizeof_t a
  ) :<f> void

(* ****** ****** *)

fun{a:t@ype} array_ptr_to_list {n:nat}
  (base: &(@[a][n]) >> @[a?][n], asz: size_t n):<> list_vt (a, n)

(* ****** ****** *)

(*
**
** persistent arrays
**
*)

(* ****** ****** *)

castfn array_make_view_ptr {a:viewt@ype} {n:nat} {l:addr}
  (pf: vbox (array_v (a, n, l)) | p: ptr l):<> array (a, n)
// end of [array_make_view_ptr]

castfn array_get_view_ptr {a:viewt@ype} {n:nat}
  (A: array (a, n)):<> [l:addr] (vbox (array_v (a, n, l)) | ptr l)
// end of [array_get_view_ptr]

(* ****** ****** *)

fun array_make_arraysize
  {a:viewt@ype} {n:nat} (arrsz: arraysize (a, n)):<> array (a, n)

macdef array (x) = array_make_arraysize ,(x)

(* ****** ****** *)

fun{a:t@ype} array_make_elt {n:nat} (asz: size_t n, elt: a):<> array (a, n)

fun{a:t@ype} array_make_lst {n:nat}
  (asz: size_t n, xs: list (a, n)):<> array (a, n)

fun{a:viewt@ype} array_make_lst_vt {n:nat}
  (asz: size_t n, xs: list_vt (a, n)):<> array (a, n)

(* ****** ****** *)

fun array_make_clo_tsz {a:viewt@ype} {n:nat} {f:eff} (
    asz: size_t n
  , f: &(&(a?) >> a, sizeLt n) -<clo,f> void
  , tsz: sizeof_t a
  ) :<f> array (a, n)

fun array_make_cloref_tsz {a:viewt@ype} {n:nat} (
    asz: size_t n
  , f: !(&(a?) >> a, sizeLt n) -<cloref1> void
  , tsz: sizeof_t a
  ) : array (a, n)

(* ****** ****** *)

fun{a:t@ype} array_get_elt_at {n:nat}
  {i:nat | i < n} (A: array (a, n), i: size_t i):<!ref> a
overload [] with array_get_elt_at

fun{a:t@ype} array_set_elt_at {n:nat}
  {i:nat | i < n} (A: array (a, n), i: size_t i, x: a):<!ref> void
overload [] with array_set_elt_at

fun{a:viewt@ype} array_xch_elt_at {n:nat}
  {i:nat | i < n} (A: array (a, n), i: size_t i, x: &a):<!ref> void

(* ****** ****** *)

fun{a:t@ype} array_get_elt_at__intsz {n:nat}
  {i:nat | i < n} (A: array (a, n), i: int i):<!ref> a
overload [] with array_get_elt_at__intsz

fun{a:t@ype} array_set_elt_at__intsz {n:nat}
  {i:nat | i < n} (A: array (a, n), i: int i, x: a):<!ref> void
overload [] with array_set_elt_at__intsz

fun{a:viewt@ype} array_xch_elt_at__intsz {n:nat}
  {i:nat | i < n} (A: array (a, n), i: int i, x: &a):<!ref> void

(* ****** ****** *)

fun{a:viewt@ype} array_exch {n:nat}
  (A: array (a, n), i: sizeLt n, j: sizeLt n):<!ref> void

(* ****** ****** *)

//
// these functions are just as easy to be implemented on the spot (HX)
//

fun{a:viewt@ype} array_foreach__main {v:view} {vt:viewtype} {n:nat} (
    pf: !v
  | f: (!v | &a, !vt) -<> void
  , A: array (a, n), asz: size_t n
  , env: !vt
  ) :<!ref> void

fun{a:viewt@ype} array_foreach_fun {v:view} {n:nat} (
    pf: !v | f: (!v | &a) -<fun> void, A: array (a, n), asz: size_t n
  ) :<!ref> void

fun{a:viewt@ype} array_foreach_clo {v:view} {n:nat} (
    pf: !v | f: &(!v | &a) -<clo> void, A: array (a, n), asz: size_t n
  ) :<!ref> void

fun{a:viewt@ype} array_foreach_cloref {v:view} {n:nat} (
    pf: !v | f: !(!v | &a) -<cloref> void, A: array (a, n), asz: size_t n
  ) :<!ref> void

(* ****** ****** *)

//
// these functions are just as easy to be implemented on the spot (HX)
//

fun{a:viewt@ype} array_iforeach__main {v:view} {vt:viewtype} {n:nat} (
    pf: !v
  | f: (!v | sizeLt n, &a, !vt) -<> void
  , A: array (a, n), asz: size_t n
  , env: !vt
  ) :<!ref> void

fun{a:viewt@ype} array_iforeach_fun {v:view} {n:nat} (
    pf: !v | f: (!v | sizeLt n, &a) -<fun> void, A: array (a, n), asz: size_t n
  ) :<!ref> void

fun{a:viewt@ype} array_iforeach_clo {v:view} {n:nat} (
    pf: !v | f: &(!v | sizeLt n, &a) -<clo> void, A: array (a, n), asz: size_t n
  ) :<!ref> void

fun{a:viewt@ype} array_iforeach_cloref {v:view} {n:nat} (
    pf: !v | f: !(!v | sizeLt n, &a) -<cloref> void, A: array (a, n), asz: size_t n
  ) :<!ref> void

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [array.sats] finishes!\n"

#endif

(* end of [array.sats] *)
