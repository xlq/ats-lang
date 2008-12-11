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

#include "prelude/params.hats"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [array.sats] starts!\n"

#endif

(* ****** ****** *)

fun{a:t@ype} atarray_get_elt_at
  {n:nat} (A: &(@[a][n]), i: natLt n):<> a

fun{a:t@ype} atarray_set_elt_at
  {n:nat} (A: &(@[a][n]), i: natLt n, x:a):<> void

overload [] with atarray_get_elt_at
overload [] with atarray_set_elt_at

(* ****** ****** *)

(*

dataview array_v (a:viewt@ype+, int, addr) =
  | {l:addr} array_v_nil (a, 0, l)
  | {n:int | n >= 0} {l:addr}
      array_v_cons (a, n+1, l) of (a @ l, array_v (a, n, l+sizeof a))

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

fun{a:viewt@ype}
  array_ptr_alloc {n:nat} (asz: int n):<>
    [l:addr | l <> null] (free_gc_v l, array_v (a?, n, l) | ptr l)

fun array_ptr_alloc_tsz
  {a:viewt@ype} {n:nat} (asz: int n, sz: sizeof_t a):<>
    [l:addr | l <> null] (free_gc_v l, array_v (a?, n, l) | ptr l)
  = "atspre_array_ptr_alloc_tsz"

fun array_ptr_free
  {a:viewt@ype} {n:int} {l:addr}
  (_: free_gc_v l, _: array_v (a?, n, l) | _: ptr l):<> void
  = "atspre_array_ptr_free" 

(* ****** ****** *)

fun{a:t@ype} array_ptr_initialize_elt {n:nat}
  (base: &(@[a?][n]) >> @[a][n], asz: int n, ini: a):<> void

fun array_ptr_initialize_elt_tsz {a:t@ype} {n:nat}
  (base: &(@[a?][n]) >> @[a][n], asz: int n, ini: &a, tsz: sizeof_t a):<> void
  = "atspre_array_ptr_initialize_elt_tsz"

fun{a:t@ype} array_ptr_initialize_lst {n:nat}
  (base: &(@[a?][n]) >> @[a][n], asz: int n, xs: list (a, n)):<> void

(* ****** ****** *)

// implemented in [prelude/DATS/array.dats]
fun array_ptr_initialize_fun_tsz_main
  {a:viewt@ype} {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | base: &(@[a?][n]) >> @[a][n]
  , asz: int n
  , f: (!v | &(a?) >> a, natLt n, !vt) -<f> void
  , tsz: sizeof_t a
  , env: !vt
  ) :<f> void
  = "atspre_array_ptr_initialize_fun_tsz_main"

(* ****** ****** *)

// implemented in [prelude/DATS/array.dats]
fun array_ptr_initialize_cloptr_tsz_main
  {a:viewt@ype} {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | base: &(@[a?][n]) >> @[a][n]
  , asz: int n
  , f: !(!v | &(a?) >> a, natLt n, !vt) -<cloptr,f> void
  , tsz: sizeof_t a
  , env: !vt
  ) :<f> void
  = "atspre_array_ptr_initialize_cloptr_tsz_main"

// implemented in [prelude/DATS/array.dats]
fun array_ptr_initialize_cloptr_tsz {a:viewt@ype} {n:nat} {f:eff} (
    base: &(@[a?][n]) >> @[a][n]
  , asz: int n
  , f: !(&(a?) >> a, natLt n) -<cloptr,f> void
  , tsz: sizeof_t a
  ) :<f> void
  = "atspre_array_ptr_initialize_cloptr_tsz"

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

fun array_ptr_takeout_tsz
  {a:viewt@ype} {n,i:nat | i < n} {l0:addr} (
    pf: array_v (a, n, l0)
  | base: ptr l0
  , offset: int i
  , tsz: sizeof_t a
  ) :<> [l:addr] (
      a @ l
    , a @ l -<lin,prf> array_v (a, n, l0)
    | ptr l
    )
  = "atspre_array_ptr_takeout_tsz"

fun array_ptr_takeout2_tsz
  {a:viewt@ype} {n,i1,i2:nat | i1 < n; i2 < n; i1 <> i2} {l0:addr} (
    pf: array_v (a, n, l0)
  | base: ptr l0
  , off1: int i1, off2: int i2
  , tsz: sizeof_t a
  ) :<> [l1,l2:addr] (
      a @ l1
    , a @ l2, (a @ l1, a @ l2) -<lin,prf> array_v (a, n, l0)
    | ptr l1
    , ptr l2
    )
  = "atspre_array_ptr_takeout2_tsz"

//

fun{a:t@ype} array_ptr_get_elt_at
  {n:nat} (A: &(@[a][n]), i: natLt n):<> a

fun{a:t@ype} array_ptr_set_elt_at
  {n:nat} (A: &(@[a][n]), i: natLt n, x: a):<> void

fun{a:viewt@ype} array_ptr_xch_elt_at
  {n,i:nat | i < n} {l:addr}
  (A: &(@[a][n]), i: int i, x: &a):<> void

//

fun array_ptr_copy_tsz {a:t@ype} {n:nat} (
    A: &(@[a][n])
  , B: &(@[a?][n]) >> @[a][n]
  , n: int n
  , tsz: sizeof_t a
  ) :<> void
  = "atspre_array_ptr_copy_tsz"

fun array_ptr_move_tsz {a:viewt@ype} {n:nat} (
    A: &(@[a][n]) >> @[a?][n]
  , B: &(@[a?][n]) >> @[a][n]
  , n: int n
  , tsz: sizeof_t a
  ) :<> void
  = "atspre_array_ptr_move_tsz"

//

fun{a:viewt@ype} array_ptr_exch
  {n,i1,i2:nat | i1 < n; i2 < n; i1 <> i2}
  (A: &(@[a][n]), i1: int i1, i2: int i2):<> void

(* ****** ****** *)

// implemented in [prelude/DATS/array.dats]
fun foreach_array_ptr_tsz_main
  {a:viewt@ype} {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | f: (!v | &a, !vt) -<f> void
  , base: &(@[a][n])
  , asz: int n
  , tsz: sizeof_t a
  , env: !vt
  ) :<f> void
  = "atspre_foreach_array_ptr_tsz_main"

fun foreach_array_ptr_tsz_cloptr
  {a:viewt@ype} {v:view} {n:nat} {f:eff} (
    pf: !v
  | f: !(!v | &a) -<cloptr,f> void
  , base: &(@[a][n])
  , asz: int n
  , tsz: sizeof_t a
  ) :<f> void

(* ****** ****** *)

// implemented in [prelude/DATS/array.dats]
fun iforeach_array_ptr_tsz_main
  {a:viewt@ype} {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | f: (!v | natLt n, &a, !vt) -<f> void
  , base: &(@[a][n])
  , asz: int n
  , tsz: sizeof_t a
  , env: !vt
  ) :<f> void
  = "atspre_iforeach_array_ptr_tsz_main"

fun iforeach_array_ptr_tsz_cloptr
  {a:viewt@ype} {v:view} {n:nat} {f:eff} (
    pf: !v
  | f: !(!v | natLt n, &a) -<cloptr,f> void
  , base: &(@[a][n])
  , asz: int n
  , tsz: sizeof_t a
  ) :<f> void

(* ****** ****** *)

fun{a:t@ype} array_ptr_to_list {n:nat}
  (base: &(@[a][n]) >> @[a?][n], asz: int n):<> list_vt (a, n)

(* ****** ****** *)

(*
 *
 * persistent arrays
 *
 *)

(* ****** ****** *)

fun array_make_arraysize
  {a:viewt@ype} {n:nat} (arrsz: arraysize (a, n)):<> array (a, n)

macdef array (x) = array_make_arraysize ,(x)

fun{a:t@ype} array_make_elt {n:nat} (asz: int n, elt: a):<> array (a, n)

fun{a:t@ype} array_make_lst {n:nat}
  (asz: int n, xs: list (a, n)):<> array (a, n)

fun array_make_cloptr_tsz {a:viewt@ype} {n:nat} {f:eff} (
    asz: int n
  , f: !(&(a?) >> a, natLt n) -<cloptr,f> void
  , tsz: sizeof_t a
  ) :<f> array (a, n)

(* ****** ****** *)

fun array_get_view_ptr {a:viewt@ype} {n:nat}
  (A: array (a, n)):<> [l:addr] (vbox (array_v (a, n, l)) | ptr l)

(* ****** ****** *)

fun{a:t@ype} array_get_elt_at {n:nat}
  (A: array (a, n), i: natLt n):<!ref> a

fun{a:t@ype} array_set_elt_at {n:nat}
  (A: array (a, n), i: natLt n, x: a):<!ref> void

fun{a:viewt@ype} array_xch_elt_at
  {n:nat} (A: array (a, n), i: natLt n, x: &a):<!ref> void

overload [] with array_get_elt_at
overload [] with array_set_elt_at

(* ****** ****** *)

fun{a:viewt@ype} array_exch
  {n:nat} (A: array (a, n), i: natLt n, j: natLt n):<!ref> void

(* ****** ****** *)

fun{a:t@ype} foreach_array_main {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | f: (!v | a, !vt) -<f> void
  , A: array (a, n), asz: int n
  , env: !vt
  ) :<f,!ref> void
overload foreach with foreach_array_main

fun{a:t@ype} foreach_array_cloptr {v:view} {n:nat} {f:eff} (
    pf: !v | f: !(!v | a) -<cloptr,f> void, A: array (a, n), asz: int n
  ) :<f,!ref> void
overload foreach with foreach_array_cloptr

fun{a:t@ype} foreach_array_cloref {v:view} {n:nat} {f:eff} (
    pf: !v | f: !(!v | a) -<cloref,f> void, A: array (a, n), asz: int n
  ) :<f,!ref> void
overload foreach with foreach_array_cloref

(* ****** ****** *)

fun{a:t@ype} iforeach_array_main {v:view} {vt:viewtype} {n:nat} {f:eff} (
    pf: !v
  | f: (!v | natLt n, a, !vt) -<f> void
  , A: array (a, n), asz: int n
  , env: !vt
  ) :<f,!ref> void
overload iforeach with iforeach_array_main

fun{a:t@ype} iforeach_array_cloptr {v:view} {n:nat} {f:eff} (
    pf: !v | f: !(!v | natLt n, a) -<cloptr,f> void, A: array (a, n), asz: int n
  ) :<f,!ref> void
overload iforeach with iforeach_array_cloptr

fun{a:t@ype} iforeach_array_cloref {v:view} {n:nat} {f:eff} (
    pf: !v | f: !(!v | natLt n, a) -<cloref,f> void, A: array (a, n), asz: int n
  ) :<f,!ref> void
overload iforeach with iforeach_array_cloref

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [array.sats] finishes!\n"

#endif

(* end of [array.sats] *)
