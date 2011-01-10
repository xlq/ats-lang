(*
** Some simple testing code
*)

(* ****** ****** *)

staload "contrib/testing/SATS/randgen.sats"
staload _(*anon*) = "contrib/testing/DATS/randgen.dats"

(* ****** ****** *)

#include "insort_arr.dats"

(* ****** ****** *)

staload "libc/SATS/random.sats"

(* ****** ****** *)

typedef T = double

(* ****** ****** *)

implement randgen<T> () = drand48 ()

(* ****** ****** *)

fun print_array {n:nat}
  {i:nat | i <= n} {l:addr} (
    A: &(@[T][n]), n: int n, i: int i
  ) : void = let
  var i: natLte (n)
in
  for (i := 0; i < n; i := i+1) (
    if i > 0 then print ", "; print (A.[i])
  ) // end of [for]
end // end of [print_array]

(* ****** ****** *)

implement
main () = () where {
//
  val () = srand48_with_time ()
//
  #define N 10
//
  var !p_arr with pf_arr = @[T][N]()
  val () = array_randinit<T> (pf_arr | p_arr, N)
//
  val () = print_array (!p_arr, N, 0)
  val () = print_newline ()
//
  prval pflen = gfarray_of_array {T} (pf_arr)
//
  extern fun lte
    (x1: &T, x2: &T): bool = "test_lte"
  implement lte (x1, x2) = x1 <= x2
  extern fun lte {x1,x2:int}
    (x1: &elt (T, x1), x2: &elt (T, x2)): bool (x1 <= x2) = "test_lte"
//
  val (pfsrt | ys) = insort<T> (pflen, pf_arr | p_arr, N, lte)
  prval pfperm = SORT2PERM (pfsrt)
  prval pflen = permute_length_lemma (pfperm, pflen)
  prval pflen_alt = array_of_gfarray {T} (pf_arr)
  prval () = length_isfun (pflen, pflen_alt)
//
  val () = print_array (!p_arr, N, 0)
  val () = print_newline ()
//
} // end of [main]

(* ****** ****** *)

(* end of [test_insort_arr.dats] *)
