(*
**
** An Example of Stack Algebra
** See Section 8.5.2 in Dines Bjorner's SE book
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2010
**
*)

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no staloading at run-time

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"
stadef nil = ilist_nil // creating a shorthand
stadef cons = ilist_cons // creating a shorthand

(* ****** ****** *)

staload "stack_alg.sats"

(* ****** ****** *)

abst@ype E (a:t@ype, x:int) = a
castfn encelt {a:t@ype} (x: a):<> [i:int] E (a, i)
castfn decelt {a:t@ype} {i:int} (x: E (a, i)):<> a

(* ****** ****** *)
//
// HX-2010-12-07:
// [n] is the number of available slots
//
absviewtype Stack (a:t@ype, xs:ilist, n:int)

(* ****** ****** *)

fun{a:t@ype}
make_nil {n:nat}
  (n: int n): [xs:ilist] (EMPTY (xs) | Stack (a, xs, n))
// end of [make_nil]

fun{a:t@ype} free_nil {n:nat} (s: Stack (a, nil, n)): void

(* ****** ****** *)

fun{a:t@ype}
is_empty {xs:ilist} {n:nat}
  (s: Stack (a, xs, n)): [b:bool] (IS_EMPTY (xs, b) | bool (b))
// end of [is_empty]

fun{a:t@ype}
length {xs:ilist} {n:nat}
  (s: !Stack (a, xs, n)): [m:nat] (LENGTH (xs, m) | int m)
// end of [length]

fun{a:t@ype}
top {xs:ilist} {n:nat} (
  pf: IS_EMPTY (xs, false) | s: !Stack (a, xs, n)
) : [x:int] (TOP (xs, x) | E (a, x)) // end of [top]

fun{a:t@ype}
pop {xs1:ilist} {n:nat} (
  pf: IS_EMPTY (xs1, false)
| s: !Stack (a, xs1, n) >> Stack (a, xs2, n+1)
) : #[xs2:ilist] (POP (xs1, xs2) | void) // end of [pop]

fun{a:t@ype}
push {x:int} {xs1:ilist} {n:pos} (
  e: E (a, x), s: !Stack (a, xs1, n) >> Stack (a, xs2, n-1)
): #[xs2:ilist] (PUSH (x, xs1, xs2) | void) // end of [push]

(* ****** ****** *)

(* end of [stack_array.sats] *)
