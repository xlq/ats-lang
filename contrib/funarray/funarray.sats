(*
**
** An implementation of functional arrays based on Braun trees.
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2008
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt
//

(* ****** ****** *)

abstype funarray (t@ype+ (*element*),  int (*size*))

typedef farr (a: t@ype, n: int) = funarray (a, n) // an abbreviation

(* ****** ****** *)

fun funarray_nil {a:t@ype} (): farr (a, 0)

(* ****** ****** *)

fun{a:t@ype} funarray_length (* O(log^2(n)) *)
  {n:nat} (A: farr (a, n)):<(*pure*)> int n

(* ****** ****** *)

fun{a:t@ype} funarray_get_elt_at (* O(log(n)) *)
  {n:nat} (A: farr (a, n), i: natLt n):<(*pure*)> a

fun{a:t@ype} funarray_set_elt_at (* O(log(n)) *)
  {n:nat} (A: farr (a, n), i: natLt n, x: a):<(*pure*)> farr (a, n)

overload [] with funarray_get_elt_at
overload [] with funarray_set_elt_at
  
(* ****** ****** *)

fun{a:t@ype} funarray_loadd (* O(log(n)) *)
  {n:nat} (A: farr (a, n), x: a):<(*pure*)> farr (a, n+1)

fun{a:t@ype} funarray_lorem (* O(log(n)) *)
  {n:pos} (A: farr (a, n)):<(*pure*)> farr (a, n-1)

fun{a:t@ype} funarray_lorem_get (* O(log(n)) *)
  {n:pos} (A: farr (a, n), x: &a? >> a):<(*pure*)> farr (a, n-1)

(* ****** ****** *)

fun{a:t@ype} funarray_hiadd (* O(log(n)) *)
  {n:nat} (A: farr (a, n), n: int n, x: a):<(*pure*)> farr (a, n+1)

fun{a:t@ype} funarray_hirem (* O(log(n)) *)
  {n:pos} (A: farr (a, n), n: int n):<(*pure*)> farr (a, n-1)

fun{a:t@ype} funarray_hirem_get (* O(log(n)) *)
  {n:pos} (A: farr (a, n), n: int n, x: &a? >> a):<(*pure*)> farr (a, n-1)

(* ****** ****** *)

(* end of [funarray.sats] *)
