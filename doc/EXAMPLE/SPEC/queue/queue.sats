(*
**
** An Example of Stack Algebra
** See Section 8.5.3 in Dines Bjorner's SE book
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2010
**
*)

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"
stadef nil = ilist_nil // creating a shorthand
stadef cons = ilist_cons // creating a shorthand

(* ****** ****** *)

dataprop
IS_EMPTY (ilist, bool) =
  | IS_EMPTY_nil (nil, true)
  | {x:int} {xs:ilist} IS_EMPTY_cons (cons (x, xs), false)
// end of [IS_EMPTY]

(* ****** ****** *)

dataprop
DEQUE (ilist, ilist, int) =
  | {x0:int} {xs1,xs2:ilist} {x:int}
    DEQUEcons (cons (x0, xs1), cons (x0, xs2), x) of DEQUE (xs1, xs2, x)
  | {x:int} DEQUEnil (cons (x, nil), nil, x)
// end of [DEQUE]

(* ****** ****** *)

abst@ype E (a:t@ype, x:int) = a
castfn encelt {a:t@ype} (x: a):<> [i:int] E (a, i)
castfn decelt {a:t@ype} {i:int} (x: E (a, i)):<> a

(* ****** ****** *)

absviewtype Queue (a:t@ype, xs:ilist)
viewtypedef Queue (a:t@ype) = [xs:ilist] Queue (a, xs)

(* ****** ****** *)

fun{a:t@ype} empty (): Queue (a, nil)

fun{a:t@ype}
is_empty {xs:ilist}
  (q: !Queue (a, xs)): [b:bool] (IS_EMPTY (xs, b) | bool b)
// end of [is_empty]

fun{a:t@ype}
enque {x:int} {xs:ilist} (
  e: E (a, x), q: !Queue (a, xs) >> Queue (a, cons (x, xs))
) : void // end of [enque]

fun{a:t@ype}
deque {xs:ilist} (
  pf: IS_EMPTY (xs, false) | q: !Queue (a, xs) >> Queue (a, xs1)
) : #[x:int;xs1:ilist] (DEQUE (xs, xs1, x) | E (a, x))
// end of [deque]

(* ****** ****** *)

fun{a:t@ype} free_nil (q: Queue (a, nil)): void

(* ****** ****** *)

(* end of [queue.sats] *)
