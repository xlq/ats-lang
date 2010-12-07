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

staload "libats/SATS/ilistp.sats"

(* ****** ****** *)

stadef nil = ilist_nil // creating a shorthand
stadef cons = ilist_cons // creating a shorthand

// this specifies what EMPTY does
dataprop EMPTY (ilist) = EMPTY (nil)

// this specifies what IS_EMPTY does
dataprop
IS_EMPTY (ilist, bool) =
  | IS_EMPTY_nil (nil, true)
  | {x:int} {xs:ilist} IS_EMPTY_cons (cons (x, xs), false)
// end of [IS_EMPTY]

// this specifies what TOP does
dataprop TOP (ilist, int) =
  | {x:int} {xs:ilist} TOP (cons (x, xs), x)
// end of [TOP]

// this specifies what POP does
dataprop POP (ilist, ilist) =
  | {x:int} {xs:ilist} POP (cons (x, xs), xs)
// end of [POP]

// this specifies what PUSH does
dataprop PUSH (int, ilist, ilist) =
  | {x:int} {xs:ilist} PUSH (x, xs, cons (x, xs))
// end of [PUSH]

(* ****** ****** *)

abst@ype E (a:t@ype, x:int) = a
castfn encelt {a:t@ype} (x: a):<> [i:int] E (a, i)
castfn decelt {a:t@ype} {i:int} (x: E (a, i)):<> a

(* ****** ****** *)

abstype Stack (a:t@ype, xs:ilist)
typedef Stack (a:t@ype) = [xs:ilist] Stack (a, xs)

(* ****** ****** *)

fun{a:t@ype}
empty (): [xs:ilist] (EMPTY (xs) | Stack (a, xs))

fun{a:t@ype}
is_empty {xs:ilist}
  (s: Stack (a, xs)): [b:bool] (IS_EMPTY (xs, b) | bool (b))
// end of [is_empty]

fun{a:t@ype}
top {xs:ilist}
  (pf: IS_EMPTY (xs, false) | s: Stack (a, xs)): [x:int] (TOP (xs, x) | E (a, x))
// end of [top]

fun{a:t@ype}
pop {xs1:ilist}
  (pf: IS_EMPTY (xs1, false) | s: Stack (a, xs1)): [xs2:ilist] (POP (xs1, xs2) | Stack (a, xs2))
// end of [pop]

fun{a:t@ype}
push {x:int} {xs1:ilist}
  (e: E (a, x), s: Stack (a, xs1)): [xs2:ilist] (PUSH (x, xs1, xs2) | Stack (a, xs2))
// end of [push]

(* ****** ****** *)

(* end of [stack.sats] *)
