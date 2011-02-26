//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
(* ****** ****** *)

staload "contrib/linux/basics.sats"

(* ****** ****** *)

staload "libats/ngc/SATS/slist.sats"
staload "contrib/linux/utils/SATS/array.sats"

(* ****** ****** *)

staload "scull.sats"

(* ****** ****** *)

(*
fun qset_dataptr_free
  {m,n:nat} (p: qset_dataptr (m, n), m: size_t m): void
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
) :<> void = "atsctrb_linux_array_ptr_kfree"
//
fun free_agz {l:agz} (
  pf: qset_data_v (m, n, l) | p: ptr l, m: size_t m
) : void = let
  prval (pfgc, pfarr) = qset_data_v_takeout_all (pf)
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



(* ****** ****** *)

(* end of [scull.dats] *)
