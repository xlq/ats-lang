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

// this is originally done for the ATS/CBLAS package

(* ****** ****** *)

//
// legend:
// S: single precision float (float)
// D: double precision float (double)
// C: single precision complex (ccmplx)
// Z: double precision complex (zcmplx)
//

(* ****** ****** *)

// S, D, C, Z
fun{a:t@ype} print_typ (): void
fun{a:t@ype} print_elt (x: a): void

(* ****** ****** *)

// S, D, C, Z
fun{a:t@ype} of_int (x: int):<> a

(* ****** ****** *)

// S, D
fun{a:t@ype} of_size (x: size_t):<> a

(* ****** ****** *)

// S, D, C, Z
fun{a:t@ype} of_double (x: double):<> a

(* ****** ****** *)

// S, D
fun{a:t@ype} to_int (x:a):<> int
fun{a:t@ype} to_float (x: a):<> float
fun{a:t@ype} to_double (x: a):<> double

(* ****** ****** *)

// S, D, C, Z
fun{a1,a2:t@ype} abs (x: a1):<> a2

(* ****** ****** *)

// S, D, C, Z
fun{a:t@ype} neg (x: a):<> a

(* ****** ****** *)

// S, D, C, Z
fun{a:t@ype} add (x1: a, x2: a):<> a
fun{a:t@ype} sub (x1: a, x2: a):<> a
fun{a:t@ype} mul (x1: a, x2: a):<> a
fun{a:t@ype} div (x1: a, x2: a):<> a

(* ****** ****** *)

// S, D
fun{a:t@ype} ceil (x:a) :<> a
fun{a:t@ype} floor (x:a) :<> a

(* ****** ****** *)

// (S, S), (D, D)
// (S, C), (C, C), (D, Z), (Z, Z)
fun{a1,a2:t@ype} scal (x1: a1, x2: a2):<> a2

(* ****** ****** *)

// S, D
fun{a:t@ype} lt (x1: a, x2: a):<> bool
fun{a:t@ype} lte (x1: a, x2: a):<> bool
fun{a:t@ype} gt (x1: a, x2: a):<> bool
fun{a:t@ype} gte (x1: a, x2: a):<> bool

(* ****** ****** *)

// S, D, C, Z
fun{a:t@ype} eq (x1: a, x2: a):<> bool
fun{a:t@ype} neq (x1: a, x2: a):<> bool

(* ****** ****** *)

// S, D
fun{a:t@ype} signof (x: a):<> Sgn
fun{a:t@ype} compare (x1: a, x2: a):<> Sgn

(* ****** ****** *)

// S, D
fun{a:t@ype} min (x:a, y:a):<> a
fun{a:t@ype} max (x:a, y:a):<> a

(* ****** ****** *)

// (S, C), (D, Z)
// a1 = |a2|
fun{a1,a2:t@ype} cmplx_make_cart (real: a1, imag: a1):<> a2

(* ****** ****** *)

// (S, C), (D, Z)

fun {a1,a2:t@ype} creal (x: a2):<> a1
fun {a1,a2:t@ype} cimag (x: a2):<> a1

(* ****** ****** *)

// C, Z
fun{a:t@ype} conj (x: a):<> a

(* ****** ****** *)

// S, D, C, Z
fun{a:t@ype} sin (x: a):<> a
fun{a:t@ype} cos (x: a):<> a
fun{a:t@ype} tan (x: a):<> a

(* ****** ****** *)

// S, D, C, Z
fun{a:t@ype} asin (x: a):<> a
fun{a:t@ype} acos (x: a):<> a
fun{a:t@ype} atan (x: a):<> a

(* ****** ****** *)

(* end of [number.sats] *)
