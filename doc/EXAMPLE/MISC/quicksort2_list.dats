(*
//
// A verified implementation of quicksort on lists:
// the returned output list is guaranteed to be a permutation
// of the original input
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Tuesday, October 5, 2010
//
//
// How to compile:
//   atscc -o quicksort2_list quicksort2_list.dats
//
*)

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"

(* ****** ****** *)

abst@ype T (x:int) = double

extern
fun lte_elt_elt {x,y:nat} (x: T x, y: T y):<> bool (x <= y)
overload <= with lte_elt_elt

datatype list (ilist) =
  | nil (ilist_nil)
  | {x:pos} {xs: ilist} cons (ilist_cons (x, xs)) of (T (x), list (xs))
// end of [list]

typedef list = [xs:ilist] list (xs)

(* ****** ****** *)

dataprop LB (x0:int, ilist) =
  | LBnil (x0, ilist_nil) of ()
  | {x:int | x0 <= x} {xs:ilist} LBcons (x0, ilist_cons (x, xs)) of LB (x0, xs)

dataprop UB (x0:int, ilist) =
  | UBnil (x0, ilist_nil) of ()
  | {x:int | x0 >= x} {xs:ilist} UBcons (x0, ilist_cons (x, xs)) of UB (x0, xs)

dataprop ISORD (ilist) =
  | ISORDnil (ilist_nil) of ()
  | {x:int} {xs:ilist}
    ISORDcons (ilist_cons (x, xs)) of (LB (x, xs), ISORD (xs))
// end of [ISORD]

(* ****** ****** *)

extern
fun quicksort {xs:ilist}
  (xs: list (xs)): [ys:ilist] (ISORD (ys), PERMUTE (xs, ys) | list (ys))
// end of [quicksort]
////
(* ****** ****** *)

extern
fun append {xs1,xs2:ilist}
  (xs1: list xs1, xs2: list xs2)
  : [xs3: ilist] (APPEND (xs1, xs2, xs3) | list xs3)
// end of [append]

implement
append {xs1, xs2}
  (xs1, xs2) = case+ xs1 of
  | cons {x1} (x1, xs11) => let
      val [xs31:ilist] (pf1 | xs31) = append (xs11, xs2)
    in
      (APPENDcons (pf1) | cons (x1, xs31))
    end // end of [cons]
  | nil () => (APPENDnil () | xs2)
// end of [append]  

(* ****** ****** *)

propdef PART (
  x: int, xs0: ilist, xs1: ilist, xs2: ilist, xs: ilist
) = {x0:int} {n0,n1,n2:nat} (
  MSETCNT (x0, xs0, n0), MSETCNT (x0, xs1, n1), MSETCNT (x0, xs2, n2)
) -<prf> MSETCNT (x0, xs, n0+n1+n2+b2i(x0==x))
// end of [PART]

fun qsrt {xs:ilist}
  (xs: list xs): [ys:ilist] (PERMUTE (xs, ys) | list (ys)) =
  case+ xs of
  | cons {x} {xs1} (x, xs1) => let
      val [ys:ilist] (fpf | ys) = part (x, xs1, nil (), nil ())
      prval fpf = lam {x0:int} {n:nat}
        (pf: MSETCNT (x0, xs, n)): MSETCNT (x0, ys, n) =<prf> let
        prval MSETCNTcons pf = pf
      in
         fpf (pf, MSETCNTnil, MSETCNTnil)
      end // end of [prval]
    in
      (fpf | ys)
    end // end of [cons]
  | nil () => (permute_refl {ilist_nil} () | nil ())
// end of [qsrt]

and part {x:pos} {xs,xs1,xs2:ilist} (
    x: T x, xs: list xs, xs1: list xs1, xs2: list xs2
  ) : [ys:ilist] (PART (x, xs, xs1, xs2, ys) | list ys) =
  case xs of
  | cons (x_, xs_) => (
      if (x_ <= x) then let
        val [ys:ilist] (fpf | ys) = part (x, xs_, cons (x_, xs1), xs2)
        prval fpf = lam {x0:int} {n0,n1,n2:nat}
          (pf0: MSETCNT (x0, xs, n0), pf1: MSETCNT (x0, xs1, n1), pf2: MSETCNT (x0, xs2, n2))
          : MSETCNT (x0, ys, n0+n1+n2+b2i(x0==x)) =<prf> let
          prval MSETCNTcons pf0 = pf0
          prval pf1 = MSETCNTcons (pf1)
        in
          fpf (pf0, pf1, pf2)
        end // end of [prval]
      in
        (fpf | ys)
      end else let
        val [ys:ilist] (fpf | ys) = part (x, xs_, xs1, cons (x_, xs2))
        prval fpf = lam {x0:int} {n0,n1,n2:nat}
          (pf0: MSETCNT (x0, xs, n0), pf1: MSETCNT (x0, xs1, n1), pf2: MSETCNT (x0, xs2, n2))
          : MSETCNT (x0, ys, n0+n1+n2+b2i(x0==x)) =<prf> let
          prval MSETCNTcons pf0 = pf0
          prval pf2 = MSETCNTcons (pf2)
        in
          fpf (pf0, pf1, pf2)
        end // end of [prval]
      in
        (fpf | ys)
      end // end of [let]
    ) // end of [cons]
  | nil () => let
      val [ys1:ilist] (fpf1 | ys1) = qsrt (xs1)
      val [ys2:ilist] (fpf2 | ys2) = qsrt (xs2)
      val [ys:ilist] (pf3 | ys) = append (ys1, cons (x, ys2))
      prval fpf3 = append_munion_lemma (pf3)
      prval fpf = lam {x0:int} {n0,n1,n2:nat}
        (pf0: MSETCNT (x0, xs, n0), pf1: MSETCNT (x0, xs1, n1), pf2: MSETCNT (x0, xs2, n2))
        : MSETCNT (x0, ys, n0+n1+n2+b2i(x0==x)) =<prf> let
        prval MSETCNTnil () = pf0
        prval pf1 = fpf1 (pf1) // pf1 : MSETCNT (x0, ys1, n1)
        prval pf2 = fpf2 (pf2) // pf2 : MSETCNT (x0, ys2, n2)
      in
        fpf3 (pf1, MSETCNTcons (pf2))
      end // end of [prval]
    in
      (fpf | ys)
    end // end of [nil]
// end of [part]

(* ****** ****** *)

implement quicksort (xs) = qsrt (xs)

(* ****** ****** *)

local

assume T (n:int) = double

in

implement lte_elt_elt {x,y} (x, y) = let
  extern castfn __cast (_: bool):<> bool (x <= y)
in
  __cast (lte_double_double (x, y))
end // end of [lte_elt_elt]

fn print_list (xs: list): void = let
  fun aux (xs: list, i: int): void = begin case+ xs of
    | cons (x, xs) => begin
        if i > 0 then print ", "; printf ("%.1f", @(x)); aux (xs, i+1)
      end // end of [cons]
    | nil () => ()
  end // end of [aux]
in
  aux (xs, 0)
end // end of [print_list]

castfn T .<>. (f: double):<> [x:pos] T (x) = #[1 | f]

end // end of [local]

(* ****** ****** *)

#define :: cons

implement main () = let
  val xs: list =
     T 2.0 :: T 1.0 :: T 4.0 :: T 3.0 :: T 6.0 :: T 5.0
  :: T 2.0 :: T 1.0 :: T 4.0 :: T 3.0 :: T 6.0 :: T 5.0
  :: T 2.0 :: T 1.0 :: T 4.0 :: T 3.0 :: T 6.0 :: T 5.0
  :: T 2.0 :: T 1.0 :: T 4.0 :: T 3.0 :: T 6.0 :: T 5.0
  :: nil ()
  val (_fpf | ys) = quicksort (xs)
in
  print "xs = "; print_list xs; print_newline ();
  print "ys = "; print_list ys; print_newline ();
end // end of [main]

(* ****** ****** *)

(* end of [quicksort2_list.dats] *)
