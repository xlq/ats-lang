(*
**
** An interface for various common funtion on numbers
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Shivkumar Chandrasekaran (shiv AT ece DOT ucsb DOT edu)
**
** Time: Summer, 2009
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

fun{a:t@ype} print_typ (): void
fun{a:t@ype} print_elt (x: a): void

(* ****** ****** *)

fun{a:t@ype} of_int (x: int):<> a

(* ****** ****** *)

fun{a:t@ype} of_double (x: double):<> a

(* ****** ****** *)

fun{a1,a2:t@ype} abs (x: a1):<> a2

(* ****** ****** *)

fun{a:t@ype} neg (x: a):<> a

(* ****** ****** *)

fun{a:t@ype} add (x1: a, x2: a):<> a
fun{a:t@ype} sub (x1: a, x2: a):<> a
fun{a:t@ype} mul (x1: a, x2: a):<> a
fun{a:t@ype} div (x1: a, x2: a):<> a

(* ****** ****** *)

fun{a1,a2:t@ype} scal (x1: a1, x2: a2):<> a2

(* ****** ****** *)

fun{a:t@ype} eq (x1: a, x2: a):<> bool
fun{a:t@ype} neq (x1: a, x2: a):<> bool

(* ****** ****** *)

(* end of [number.sats] *)
