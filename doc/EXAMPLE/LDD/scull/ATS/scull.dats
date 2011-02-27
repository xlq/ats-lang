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

implement
qset_dataptr_free
  {m,n} (p, m) = let
//
viewtypedef qtmptr = qtmptr (n)
//
extern fun array_ptr_kfree
  {a:viewt@ype} {n:int} {l:addr} (
  pf_gc: kfree_v l, pf_arr: array_v (a?, n, l) | p_arr: ptr l
) :<> void = "atsctrb_kernel_array_ptr_kfree"
//
fun free_agz {l:agz} .<>. (
  pf: qset_data_v (m, n, l) | p: ptr l, m: int m
) :<> void = let
  prval (pfgc, pfarr) = qset_data_v_takeout_all (pf)
  val m = size1_of_int1 (m)
  val () = array_ptr_clear_fun<qtmptr> (!p, m, lam x => qtmptr_free (x))
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
fun qset_get_next : slnode_get_next_type (qset)
implement
slnode_get_next<qset> (pf | p) = qset_get_next (pf | p)

extern
fun qset_free : slnode_free_type (qset)
implement
slnode_free<qset> (pf | p) = qset_free (pf | p)

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

(* end of [scull.dats] *)
