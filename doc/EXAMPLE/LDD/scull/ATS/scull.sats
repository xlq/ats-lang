//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0

(* ****** ****** *)

%{#
#include "ATS/scull.cats"
%} // end of [%{#]

(* ****** ****** *)

staload "libats/ngc/SATS/slist.sats"

(* ****** ****** *)

staload "contrib/kernel/basics.sats"

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

fun qtmptr_free {n:nat}
  (p: qtmptr (n)):<> void = "scull_qtmptr_free"
// end of [qtmptr_free]

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
  {m,n:nat} (p: qset_dataptr (m, n), m: int m):<> void
// end of [qset_dataptr_free]

(* ****** ****** *)

viewtypedef
qset (m:int, n:int) =
$extype_struct
  "scull_qset_struct" of {
  data= qset_dataptr (m, n)
(*
, _rest= undefined_t
*)
} // end of [qset]
viewtypedef qsetlst (m: int, n: int, ln: int) = slist (qset (m, n), ln)

(* ****** ****** *)
//
// HX: m: qset data size; n: quantum size; ln: qsetlst length
//
(*
struct scull_dev {
  int m_qset;               // the current array size
  int n_quantum;            // the current quantum size
//
  struct scull_qset *data;  // pointer to first quantum set
  int ln_qlst;              // the current qsetlst length
//
  unsigned long size;       // amount of data stored here
//
  unsigned int access_key;  // used by sculluid and scullpriv
//
  struct semaphore sem;     // mutual exclusion semaphore
//
  struct cdev cdev;	    // char device structure
//
} ; // end of [scull_dev]
*)
viewtypedef
scull_dev (
  m: int
, n: int
, ln: int
, sz: int
) =
$extype_struct
  "scull_dev_struct" of {
  empty=empty
, m_qset= int (m)
, n_quantum= int (n)
, data= qsetlst (m, n, ln)
, ln_qlst= int (ln)
, size= ulint (sz)
, _rest= undefined_vt
} // end of [scull_dev]

(* ****** ****** *)

fun scull_trim_main
  {m0,n0:nat}
  {ln:nat}
  {sz:nat}
  {m,n:pos} (
  dev: &scull_dev (m0, n0, ln, sz) >> scull_dev (m, n, 0, 0)
, m: int m
, n: int n
) : void = "scull_trim_main"

(* ****** ****** *)

(*
fun{a:vt0p}
slist_split_at
  {n:int} {i:nat | i < n} {la:addr}
  (pflst: slist_v (a, n, la) | p: ptr la, i: size_t i)
  : [lm:addr] (slseg_v (a, i, la, lm), slist_v (a, n-i, lm) | ptr lm)
// end of [slist_split_at]
*)
fun scull_follow_main
  {m,n:nat} {ln0:nat} {ln:nat} (
  xs: &slist (qset(m, n), ln0) >> slist (qset(m, n), ln0)
, ln0: &int(ln0) >> int (ln0)
, ln: int (ln)
) : #[ln0:nat;lm:addr] ptr (lm)
  = "scull_follow_main"
// end of [fun]

(* ****** ****** *)

(* end of [scull.sats] *)
