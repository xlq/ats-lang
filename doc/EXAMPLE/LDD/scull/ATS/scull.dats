//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)

staload "libats/ngc/SATS/slist.sats"
staload _(*anon*) = "libats/ngc/DATS/slist.dats"

(* ****** ****** *)

staload "contrib/linux/basics.sats"
staload "contrib/linux/SATS/utils.sats"

(* ****** ****** *)

staload "scull.sats"

(* ****** ****** *)

local

abst@ype qset = $extype "scull_qset_struct"

in // in of [local]

extern
fun qset_get_next
  : slnode_get_next_type (qset) = "scull_qset_get_next"
implement slnode_get_next<qset> (pf | p) = qset_get_next (pf | p)

extern
fun qset_set_next
  : slnode_set_next_type (qset) = "scull_qset_set_next"
implement slnode_set_next<qset> (pf | p, n) = qset_set_next (pf | p, n)

extern
fun qset_alloc
  : slnode_alloc_type (qset) = "scull_qset_alloc"
implement slnode_alloc<qset> () = qset_alloc ()

extern
fun qset_free
  : slnode_free_type (qset) = "scull_qset_free"
implement slnode_free<qset> (pf | p) = qset_free (pf | p)

end // end of [local]

(* ****** ****** *)

fun qsetlst_free
  {m,n:nat} {ln:nat}
  (xs: qsetlst (m, n, ln), m: int m): void = let
  stadef T = qset (m, n)
  stadef V = unit_v
  var !p_clo = @lam (
    pf: !V | x: &T >> T?
  ) : void =<clo> qdatptr_free (x.data, m)
  prval pfv = unit_v ()
  val () = slist_free_clo<T> {V} (pfv | xs, !p_clo)
  prval unit_v () = pfv
in
  // nothing
end // end of [qsetlst_free]

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

fun qsetlst_make
  {m,n:nat} {ln0:nat} .<>. (
  ln0: int ln0
, ln_res: &int? >> int ln
) :<> #[ln:nat | ln <= ln0] qsetlst (m, n, ln) = let
  viewtypedef qset = qset (m, n)
  fun loop {i0,j0:nat} .<i0>. (
    i0: int i0
  , res: qsetlst (m, n, j0)
  , ln_res: &int j0 >> int j
  ) :<> #[j:nat | j <= i0+j0] qsetlst (m, n, j) =
    if i0 > 0 then let
      val (pfopt | p) = slnode_alloc<qset> ()
    in
      if p > null then let
        prval Some_v (pf) = pfopt
        prval (pfat, fpf) = slnode_v_takeout_val {qset?} (pf)
        val () = p->data := qdatptr_make_null {m,n} ()
        prval () = pf := fpf (pfat)
        val res = slist_cons (pf | p, res)
        val () = ln_res := ln_res + 1
      in
        loop (i0-1, res, ln_res)
      end else let
        prval None_v () = pfopt
      in
        res
      end (* end of [if] *)
    end else res
  // end of [loop]
  val () = ln_res := 0
in
  loop (ln0, slist_nil<qset> (), ln_res)
end // end of [qsetlst_make]

(* ****** ****** *)

extern
castfn p2p {l:addr} (p: !ptr l):<> ptr l

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

(* end of [scull.dats] *)
