(*
** Some simple testing code
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list_vt.dats"
staload _(*anon*) = "libats/DATS/gflist_vt.dats"

(* ****** ****** *)

#include "mergesort_lst.dats"

(* ****** ****** *)

staload "libc/SATS/random.sats"

fun listgen {n:nat} .<n>.
  (n: int n): list_vt (double, n) =
  if n > 0 then let
    val x = drand48 () in list_vt_cons (x, listgen (n-1))
  end else list_vt_nil
// end of [listgen]

extern
fun print_list
  (xs: List (double), i: int): void = "print_list"
implement print_list (xs, i) =
  case+ xs of
  | list_cons (x, xs) => (
      if i > 0 then print ", "; print x; print_list (xs, i+1)
    ) // end of [list_cons]
  | list_nil () => ()
// end of [print_list]

extern
fun print_list_vt {n:nat}
  (xs: !list_vt (double, n), i: int): void = "print_list"

(* ****** ****** *)

implement
main () = () where {
//
  typedef T = double
//
  val () = srand48_with_time ()
//
  #define N 10
  val xs = listgen (N)
  val () = (print_list_vt (xs, 0); print_newline ())
  prval _pflen = gflist_vt_of_list_vt {T} (xs)
//
  extern fun lte
    (x1: &T, x2: &T): bool = "test_lte"
  implement lte (x1, x2) = x1 <= x2
  extern fun lte {x1,x2:int}
    (x1: &elt (T, x1), x2: &elt (T, x2)): bool (x1 <= x2) = "test_lte"
//
  val (_pfsrt | ys) = mergesort<T> (xs, lte)
//
  prval _pflen = list_vt_of_gflist_vt {T} (ys)
  val () = (print_list_vt (ys, 0); print_newline ())
//
  val () = list_vt_free (ys)
//
} // end of [main]

(* ****** ****** *)

(* end of [test_mergesort_lst.dats] *)
