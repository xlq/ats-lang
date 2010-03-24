(*
** some testing code for functions declared in
** libats/SATS/iterint.sats
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Spring, 2010
//

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "libats/SATS/iterint.sats"

(* ****** ****** *)

(*
fun foreach_clo {v:view} {n:nat} {f:eff}
  (pf: !v | n: int n, f: &(!v | natLt n) -<clo,f> void):<f> void
// end of [foreach_clo]
*)

fn sum_foreach_clo {n:nat} (n: int n): Nat = res where {
  var res: Nat = 0
  viewdef v = Nat @ res
  var !p_f = @lam
    (pf: !v | i: natLt n): void =<clo> res := res + (i+1)
  // end of [var]
  val () = foreach_clo {v} {n} (view@ res | n, !p_f)
} // end of [sum_foreach_clo]

fn test_foreach_clo () = () where {
  #define N 100
  val sum = sum_foreach_clo (N)
  val () = assert_errmsg (sum = N * (N+1) / 2, #LOCATION)
} // end of [test_foreach_clo]

(* ****** ****** *)

(*
fun foreach_cloref {n:nat} {f:eff}
  (n: int n, f: (natLt n) -<cloref,f> void):<f> void
// end of [foreach_cloref]
*)

fn sum_foreach_cloref {n:nat} (n: int n): Nat = !res where {
  val res = ref_make_elt<Nat> (0)
  val f = lam (i: natLt n): void =<cloref1> !res := !res + (i+1)
  val () = foreach_cloref {n} (n, f)
} // end of [sum_foreach_cloref]

fn test_foreach_cloref () = () where {
  #define N 100
  val sum = sum_foreach_cloref (N)
  val () = assert_errmsg (sum = N * (N+1) / 2, #LOCATION)
} // end of [test_foreach_cloref]

(* ****** ****** *)

(*
fun foreach2_clo {v:view} {m,n:nat} {f:eff}
  (pf: !v | m: int m, n: int n, f: &(!v | natLt m, natLt n) -<clo,f> void) :<f> void
// end of [foreach2_clo]
*)

fn sum_foreach2_clo {n:nat}
  (n: int n): Nat = res where {
  var res: Nat = 0
  viewdef v = Nat @ res
  var !p_f = @lam
    (pf: !v | i: natLt n, j: natLt n): void =<clo>
    res := res + (i+1) nmul (j+1)
  // end of [var]
  val () = foreach2_clo {v} {n,n} (view@ res | n, n, !p_f)
} // end of [sum_foreach2_clo]

fn test_foreach2_clo () = () where {
  #define N 100
  #define R %(N * (N+1) / 2)
  val sum = sum_foreach2_clo (N)
  val () = assert_errmsg (sum = R * R, #LOCATION)
} // end of [test_foreach2_clo]

(* ****** ****** *)

(*
fun foreach2_cloref {m,n:nat} {f:eff}
  (m: int m, n: int n, f: (natLt m, natLt n) -<cloref,f> void) :<f> void
// end of [foreach2_cloref]
*)

fn sum_foreach2_cloref {n:nat}
  (n: int n): Nat = !res where {
  val res = ref_make_elt<Nat> (0)
  val f = lam
    (i: natLt n, j: natLt n): void =<cloref1> !res := !res + (i+1) nmul (j+1)
  // end of [val]
  val () = foreach2_cloref {n,n} (n, n, f)
} // end of [sum_foreach2_cloref]

fn test_foreach2_cloref () = () where {
  #define N 100
  #define R %(N * (N+1) / 2)
  val sum = sum_foreach2_cloref (N)
  val () = assert_errmsg (sum = R * R, #LOCATION)
} // end of [test_foreach2_clo]

(* ****** ****** *)

(*
fun repeat_clo {v:view} {n:nat} {f:eff}
  (pf: !v | n: int n, f: &(!v | (*none*)) -<clo,f> void):<f> void
// end of [repeat_clo]
*)

fn sum_repeat_clo {n:nat} (n: int n): Nat = res where {
  var i: Nat = 1
  var res: Nat = 0
  viewdef v = (Nat @ i, Nat @ res)
  var !p_f = @lam
    (pf: !v | (*none*)): void =<clo> let
    prval (pf1, pf2) = pf
    val () = (res := res + i; i := i + 1)
    prval () = pf := (pf1, pf2)
  in
    // nothing
  end // end of [var]
  prval pf = (view@ i, view@ res)
  val () = repeat_clo {v} {n} (pf | n, !p_f)
  prval () = (view@ i := pf.0; view@ res := pf.1)
} // end of [sum_repeat_clo]

fn test_repeat_clo () = () where {
  #define N 111
  val sum = sum_repeat_clo (N)
  val () = assert_errmsg (sum = N * (N+1) / 2, #LOCATION)
} // end of [test_repeat_clo]

(* ****** ****** *)

(*
fun repeat_cloref
  {n:nat} {f:eff} (n: int n, f: () -<cloref,f> void):<f> void
// end of [repeat_cloref]
*)

fn sum_repeat_cloref {n:nat} (n: int n): Nat = !res where {
  val i = ref_make_elt<Nat> (1)
  val res = ref_make_elt<Nat> (0)
  val f = lam
    (): void =<cloref1> let
    val () = (!res := !res + !i; !i := !i + 1)
  in
    // nothing
  end // end of [var]
  val () = repeat_cloref {n} (n, f)
} // end of [sum_repeat_cloref]

fn test_repeat_cloref () = () where {
  #define N 111
  val sum = sum_repeat_cloref (N)
  val () = assert_errmsg (sum = N * (N+1) / 2, #LOCATION)
} // end of [test_repeat_cloref]

(* ****** ****** *)

dynload "libats/DATS/iterint.dats"

(* ****** ****** *)

implement main () = let
  val () = test_foreach_clo ()
  val () = test_foreach_cloref ()
//
  val () = test_foreach2_clo ()
  val () = test_foreach2_cloref ()
//
  val () = test_repeat_clo ()
  val () = test_repeat_cloref ()
in
  print "[libats_iterint] testing passes!"; print_newline ()
end // end of [main]

(* ****** ****** *)

(* end of [libats_iterint.dats] *)
