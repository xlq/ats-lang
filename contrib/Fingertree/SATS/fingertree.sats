(*
**
** A finger tree implementation in ATS 
**
** Contributed by
**   Robbie Harwood (rharwood AT cs DOT bu DOT edu)
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** Time: Fall, 2010
**
*)

(* ****** ****** *)
//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//
(* ****** ****** *)

abstype
tree_t0ype_int_type (a:t@ype+, n:int)
typedef tree
  (a:t@ype, n:int) = tree_t0ype_int_type (a, n)
// end of [tree]

(* ****** ****** *)

fun{} tree_nil {a:t@ype} ():<> tree (a, 0)

fun{} tree_is_nil
  {a:t@ype} {n:nat} (xt: tree (a, n)): bool (n==0)
// end of [tree_is_nil]

(* ****** ****** *)

fun{a:t@ype}
tree_cons {n:nat}
  (x: a, xt: tree (a, n)):<> tree (a, n+1)
// end of [fingertree0_cons]

fun{a:t@ype}
tree_uncons {n:pos}
  (xt: tree (a, n), r: &a? >> a):<> tree (a, n-1)
// end of [tree_uncons]

(* ****** ****** *)

fun{a:t@ype}
tree_snoc {n:nat}
  (xt: tree (a, n), x: a):<> tree (a, n+1)
// end of [fingertree0_snoc]

fun{a:t@ype}
tree_unsnoc {n:pos}
  (xt: tree (a, n), r: &a? >> a):<> tree (a, n-1)
// end of [tree_unsnoc]

(* ****** ****** *)

fun tree_append {a:t@ype} {n1,n2:nat}
  (xt1: tree (a, n1), xt2: tree (a, n2)):<> tree (a, n1+n2)
// end of [tree_append]

(* ****** ****** *)

(* end of [fingertree.sats] *)
