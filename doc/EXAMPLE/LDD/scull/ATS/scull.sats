//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0

(* ****** ****** *)

staload "libats/ngc/SATS/slist.sats"

(* ****** ****** *)

staload "contrib/linux/basics.sats"

(* ****** ****** *)

propdef takeout_p
  (v1: view, v2: view) = v1 -<prf> (v2, v2 -<lin,prf> v1)
// end of [takeout_p]

(* ****** ****** *)
//
// HX:
// n: quantum size; l: location
//
absviewtype
qtmptr (n: int) = ptr
absview qtm_v (n: int, l:addr)

prfun qtm_v_nil {n:nat} (): qtm_v (n, null)
prfun qtm_v_takeout
  {n:nat} {l:agz} () : takeout_p (qtm_v (n, l), bytes (n) @ l)
// end of [qtm_v]

fun qtmptr_free {n:nat} (p: qtmptr (n)):<> void

(* ****** ****** *)
//
// HX:
// m: qset data size; n: quantum size; l: location
//
absviewtype
qset_dataptr (m: int, n: int) = ptr
absview qset_data_v (m: int, n: int, l:addr)

castfn qset_dataptr_encode :
  {m,n:nat} {l:addr} (qset_data_v (m, n, l) | ptr l) -<> qset_dataptr (m, n)
castfn qset_dataptr_decode :
  {m,n:nat} (qset_dataptr (m, n)) -<> [l:agez] (qset_data_v (m, n, l) | ptr l)

prfun qset_data_v_nil
  {m,n:nat} (): qset_data_v (m, n, null)
prfun qset_data_v_unnil
  {m,n:int} (pf: qset_data_v (m, n, null)): void

prfun qset_data_v_takeout {m,n:nat} {l:agz} ()
  : takeout_p (qset_data_v (m, n, l), array_v (qtmptr (n), m, l))
// end of [qset_data_v_takeout]

prfun qset_data_v_takeout_all {m,n:nat} {l:agz}
  (pf : qset_data_v (m, n, l)): (kfree_v l, array_v (qtmptr (n), m, l))
// end of [qset_data_v_takeout_all]

fun qset_dataptr_free
  {m,n:nat} (p: qset_dataptr (m, n), m: size_t m): void
// end of [qset_dataptr_free]

(* ****** ****** *)

absviewt@ype qset
viewdef qsetlst (ln: int) = slist (qset, ln)

(* ****** ****** *)

(* end of [scull.sats] *)
