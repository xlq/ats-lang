//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)

staload "myheader.sats"

(* ****** ****** *)

staload "libats/ngc/SATS/slist.sats"
staload _(*anon*) = "libats/ngc/DATS/slist.dats"

(* ****** ****** *)

staload "contrib/linux/basics.sats"
staload "contrib/linux/SATS/utils.sats"

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"
macdef viewout_decode = $UN.viewout_decode

(* ****** ****** *)

staload
UACC = "contrib/linux/asm/SATS/uaccess.sats"
macdef copy_to_user = $UACC.copy_to_user
macdef copy_from_user = $UACC.copy_from_user

(* ****** ****** *)

staload "scull.sats"

(* ****** ****** *)

#include "scull_qsetlst.hats"

(* ****** ****** *)

extern castfn p2p {l:addr} (p: !ptr l):<> ptr l

(* ****** ****** *)

implement
scull_trim_main
  (dev, m, n) = let
  val m0 = dev.m_qset
  val () = qsetlst_free (dev.data, m0)
  val () = dev.m_qset := m
  val () = dev.n_quantum := n
  val () = dev.data := slist_nil ()
  val () = dev.ln_qlst := 0
  val () = dev.size := 0UL
in
  // nothing
end // end of [scull_trim_main]

(* ****** ****** *)

implement
scull_follow_lessthan
  {m,n}
  {ln0}
  {ln} (
  xs, ln
) : [lm:agz] (
  viewout (qset(m, n) @ lm) | ptr lm
) = (pfout | pm) where {
  viewtypedef qset = qset (m, n)
  prval (pflst | ()) = slist_unfold {qset} (xs)
  val p_xs = p2p (xs)
  val ln = size1_of_int1 (ln)
  val [lm:addr] (pf1, pf2 | pm) =
    slist_split_at<qset> (pflst | p_xs, ln)
//
  prval slseg_v_cons (pf21, pf22) = pf2
  prval (pfat, fpf21) = slnode_v_takeout_val {qset} (pf21)
  prval pfout = $UN.vtakeout {qset @ lm} (pfat)
  prval () = pf21 := fpf21 (pfat)
  prval pf2 = slseg_v_cons (pf21, pf22)
//
  prval () = slist_fold {qset} (slseg_v_append (pf1, pf2) | xs)
} // end of [scull_follow_lessthan]

implement
scull_follow_main
  {m,n} {ln0} {ln}
  (xs, ln0, ln) = let
  viewtypedef qset = qset (m, n)
in
  if ln < ln0 then let
    val (pfout | pm) =
      scull_follow_lessthan (xs, ln)
    // end of [val]
  in
    (Some_v (pfout) | pm)
  end else let
    val df = ln-ln0
    var ln0_add: int?
    val xs_add = qsetlst_make (df+1, ln0_add)
    val () = ln0 := ln0 + ln0_add
  in
    if ln0_add > df then let
      val (pfout | pm) =
        scull_follow_lessthan (xs_add, df)
      // end of [val]
      val () = xs := slist_append<qset> (xs, xs_add)
    in
      (Some_v (pfout) | pm)
    end else let
      val () = xs := slist_append<qset> (xs, xs_add)
    in
      (None_v () | null) // out-of-memory
    end // end of [if]
  end // end of [if]
end // end of [scull_follow_main]

(* ****** ****** *)

macdef ENOMEM = $extval (Pos, "ENOMEM")
macdef EFAULT = $extval (Pos, "EFAULT")

extern
fun add_loff_int {i,j:int}
  (x: loff_t i, y: int j): loff_t (i+j) = "mac#add_loff_int"
// end of [fun]

(* ****** ****** *)

implement
scull_read_main
  {m,n}
  {ln0}
  {lb}
  {cnt}
  {tot} (
  pfbuf
| m, n, xs, ln, i, j, pbf, cnt, fpos
) = let
  stadef qset = qset (m, n)
  val [lm:addr] (pfout | pm) = scull_follow_lessthan {m,n} (xs, ln)
  prval (pfqs, fpfqs) = viewout_decode {qset@lm} (pfout)
  val (pfopt | pqtm) = qdatptr_vtakeout_bytes_read (pm->data, i)
  prval () = fpfqs (pfqs)
in
  if pqtm > null then let
    prval Some_v pfout = pfopt
    prval (pf, fpf) = viewout_decode (pfout)
    stavar j: int
    val j = j : int j
    prval (pf1, pf2) = bytes_v_split {n} {j} (pf)
    val [cnt:int] cnt = imin (cnt, n-j)
(*
    prval () = verify_constraint {n-j > 0} ()
*)
    val cnt_ul = $UN.cast {ulint(cnt)} (cnt)
    val nleft = copy_to_user (pfbuf | pbf, !(pqtm+j), cnt_ul)
    prval () = fpf (bytes_v_unsplit (pf1, pf2))
  in
    if nleft = 0UL then let
      val () = fpos := add_loff_int (fpos, cnt) in #[cnt | cnt]
    end else let
      val [x:int] x = EFAULT in #[~x | ~x]
    end // end of [if]
  end else let
    prval None_v () = pfopt
  in
    #[0 | 0] (* unavailable *)
  end // end of [if]
end // end of [scull_read_main]
  
(* ****** ****** *)

implement
scull_write_main
  {m,n}
  {ln0,ln}
  {lbf}
  {cnt}
  {tot} (
  pfbuf
| m, n, xs, ln0, ln, i, j, pbf, cnt, fpos
) = let
  val (pfopt | pm) = scull_follow_main (xs, ln0, ln)
  stavar ln1: int
  val ln1 = ln0: int (ln1)
in
//
if pm > null then let
  prval Some_v pfout = pfopt
  prval (pf, fpf) = viewout_decode (pfout)
  val (pfopt | pqtm) = qdatptr_vtakeout_bytes_write (pm->data, m, n, i, 0)
  prval () = fpf (pf)
in
  if pqtm > null then let  
    prval Some_v pfout = pfopt
    prval (pf, fpf) = viewout_decode (pfout)
    stavar j: int
    val j = j : int j
    prval (pf1, pf2) = bytes_v_split {n} {j} (pf)
    val [cnt:int] cnt = imin (cnt, n-j)
(*
    prval () = verify_constraint {n-j > 0} ()
*)
    val cnt_ul = $UN.cast {ulint(cnt)} (cnt)
    val nleft = copy_from_user (pfbuf | !(pqtm+j), pbf, cnt_ul)
    prval () = fpf (bytes_v_unsplit (pf1, pf2))
  in
    if nleft = 0UL then let
      val () = fpos := add_loff_int (fpos, cnt) in #[ln1, cnt | cnt]
    end else let
      val [x:int] x = EFAULT in #[ln1, ~x | ~x]
    end // end of [if]
  end else let
    prval None_v () = pfopt
    val [x:int] x = ENOMEM in #[ln1, ~x | ~x] // out-of_memory
  end (* end of [if] *)
end else let
  prval None_v () = pfopt
  val [x:int] x = ENOMEM in #[ln1, ~x | ~x] // out-of_memory
end (* end of [if] *)
//
end // end of [scull_write_main]
  
(* ****** ****** *)

(* end of [scull.dats] *)
