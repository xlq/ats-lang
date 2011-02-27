//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)

(*
staload
"prelude/SATS/array.sats" // loaded by atsopt
*)
staload _(*anon*) = "prelude/DATS/array.dats"

(* ****** ****** *)

staload "libats/ngc/SATS/slist.sats"
staload _(*anon*) = "libats/ngc/DATS/slist.dats"

(* ****** ****** *)

staload "contrib/kernel/basics.sats"
staload "contrib/kernel/SATS/utils.sats"

(* ****** ****** *)

staload "scull.sats"

(* ****** ****** *)

(*
fun qset_dataptr_free
  {m,n:nat} (p: qset_dataptr (m, n), m: int m): void
// end of [qset_dataptr_free]
*)

fun qset_dataptr_nil
  {m,n:nat} .<>. ():<> qset_dataptr (m,n) = let
  prval pf = qset_data_v_nil () in qset_dataptr_encode (pf | null)
end // end of [fun]

implement
qset_dataptr_free
  {m,n} (p, m) = let
//
viewtypedef qtmptr = qtmptr (n)
//
extern fun array_ptr_kfree
  {a:viewt@ype} {n:int} {l:addr} (
  pf_gc: kfree_v l, pf_arr: array_v (a?, n, l) | p_arr: ptr l
) :<> void = "#atsctrb_kernel_array_ptr_kfree"
//
fun free_agz {l:agz} .<>. (
  pf: qset_data_v (m, n, l) | p: ptr l, m: int m
) :<> void = let
  prval (pfgc, pfarr) = qset_data_v_takeout_all (pf)
  val m = size1_of_int1 (m)
  val () = array_ptr_clear_fun<qtmptr> (!p, m, lam x =<fun> qtmptr_free (x))
in
  array_ptr_kfree {ptr} (pfgc, pfarr | p)
end // end of [free_agz]
//
val (pf | p) = qset_dataptr_decode (p)
//
in
  if p > null then
    free_agz (pf | p, m)
  else let
    prval () = qset_data_v_unnil (pf)
  in
    // nothing
  end (* end of [if] *)
end // end of [qset_dataptr_free]

(* ****** ****** *)

local

abst@ype qset = $extype "scull_qset_struct"

in

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
  ) : void =<clo> qset_dataptr_free (x.data, m)
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
        val () = p->data := qset_dataptr_nil {m,n} ()
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

(*
fun scull_follow_main
  {m,n:nat}
  {ln0:int}
  {ln:nat | ln < ln0} (
  xs: &qsetlst (m, n, ln0) >> qsetlst (m, n, ln)
, ln: int ln
) :<> #[ln0:int | ln < ln] qsetlst (m, n, ln0-ln)
  = "scull_follow_main"
*)

fun scull_follow_main_lt
  {m,n:nat}
  {ln0:int}
  {ln:nat | ln < ln0} (
  xs: !slist (qset(m, n), ln0), ln: int (ln)
) : [lm:addr] ptr (lm) = pm where {
  viewtypedef qset = qset (m, n)
  prval (pflst | ()) = slist_unfold {qset} (xs)
  val p_xs = p2p (xs)
  val ln = size1_of_int1 (ln)
  val (pf1, pf2 | pm) = slist_split_at<qset> (pflst | p_xs, ln)
  prval () = slist_fold {qset} (slseg_v_append (pf1, pf2) | xs)
} // end of [scull_follow_main_lt]

implement
scull_follow_main
  {m,n} {ln0} {ln}
  (xs, ln0, ln) = let
  viewtypedef qset = qset (m, n)
in
  if ln < ln0 then
    scull_follow_main_lt (xs, ln)
  else let
    var ln0_new: int?
    val xs_new = qsetlst_make (ln-ln0+1, ln0_new)
    val () = xs := slist_append<qset> (xs, xs_new)
    val () = ln0 := ln0 + ln0_new
  in
    if ln < ln0 then
      scull_follow_main_lt (xs, ln)
    else null (* out-of-memory *)
  end // end of [if]
end // end of [scull_follow_main]

(* ****** ****** *)

(* end of [scull.dats] *)
