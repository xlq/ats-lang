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
tree_t0ype_int (a:t@ype+, n:int)
typedef tree
  (a:t@ype, n:int) = tree_t0ype_int (a, n)
// end of [tree]

(* ****** ****** *)

fun{}
tree_nil {a:t@ype} ():<> tree (a, 0)

fun{a:t@ype}
tree_cons {n:nat}
  (x: a, xt: tree (a, n)):<> tree (a, n+1)
// end of [fingertree0_cons]

fun{a:t@ype}
tree_uncons {n:pos}
  (xt: tree (a, n), r: &a? >> a):<> tree (a, n-1)
// end of [tree_uncons]

(* ****** ****** *)

fun{} tree_is_nil
  {a:t@ype} {n:nat} (xt: tree (a, n)): bool (n==0)
// end of [tree_is_nil]

(* ****** ****** *)

(* end of [fingertree.sats] *)
