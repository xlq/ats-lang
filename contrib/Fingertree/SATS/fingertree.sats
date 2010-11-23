(*
**
** A finger tree implementation in ATS 
**
** Contributed by
**   Robbie Harwood (rharwood AT cs DOT bu DOT edu)
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** Time: Fall, 2010
**
*)

(* ****** ****** *)
//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//
(* ****** ****** *)

datatype ftnode
  (a:t@ype+, int(*d*), int(*n*)) =
  | FTN1 (a, 0, 1) of (a) // singleton
  | {d:nat} {n1,n2:nat}
    FTN2 (a, d+1, n1+n2) of
      (ftnode (a, d, n1), ftnode (a, d, n2))
  | {d:nat} {n1,n2,n3:nat}
    FTN3 (a, d+1, n1+n2+n3) of (
      ftnode (a, d, n1), ftnode (a, d, n2), ftnode (a, d, n3)
    ) // end of [N3]
// end of [ftnode]

(* ****** ****** *)

datatype ftdigit
  (a:t@ype+, int(*d*), int(*n*)) =
  | {d:nat} {n:nat}
    FTD1 (a, d, n) of ftnode (a, d, n)
  | {d:nat} {n1,n2:nat}
    FTD2 (a, d, n1+n2) of (ftnode (a, d, n1), ftnode (a, d, n2))
  | {d:nat} {n1,n2,n3:nat}
    FTD3 (a, d, n1+n2+n3) of
      (ftnode (a, d, n1), ftnode (a, d, n2), ftnode (a, d, n3))
  | {d:nat} {n1,n2,n3,n4:nat}
    FTD4 (a, d, n1+n2+n3+n4) of (
      ftnode (a, d, n1), ftnode (a, d, n2), ftnode (a, d, n3), ftnode (a, d, n4)
    ) // end of [FTD4]
// end of [ftdigit]

(* ****** ****** *)

datatype
fingertree (a:t@ype, int(*d*), int(*n*)) =
  | {d:nat}
    FTempty (a, d, 0) of () // FTempty: () -> fingertree (a)
  | {d:nat} {n:int}
    FTsingle (a, d, n) of
      ftnode (a, d, n) // FTsingle: ftnode (a) -> fingertree (a)
  | {d:nat} {npr,nm,nsf:nat}
    FTdeep (a, d, npr+nm+nsf) of (
      ftdigit(a, d, npr), fingertree (a, d+1, nm), ftdigit (a, d, nsf)
    ) // end of [FTdeep]
// end of [fingertree]

typedef fingertree0 (a:t@ype, n:int) = fingertree (a, 0, n)

(* ****** ****** *)

fun fingertree_cons
  {a:t@ype} {d:nat} {n1,n2:int} (
  xn: ftnode (a, d, n1), xt: fingertree (a, d, n2)
) :<> fingertree (a, d, n1+n2) // end of [fingertree_cons]

fun{a:t@ype}
fingertree0_cons {n:nat}
  (x: a, xt: fingertree0 (a, n)):<> fingertree0 (a, n+1)
// end of [fingertree0_cons]

(* ****** ****** *)

fun fingertree_uncons
  {a:t@ype} {d:nat} {n:pos} (
  xt: fingertree (a, d, n), r: &ftnode? >> ftnode (a, d, n1)
) :<> #[n1:nat] fingertree (a, d, n-n1)
// end of [fingertree_uncons]

fun{a:t@ype}
fingertree0_uncons {n:pos}
  (xt: fingertree0 (a, n), r: &a? >> a):<> fingertree0 (a, n-1)
// end of [fingertree0_uncons]

(* ****** ****** *)

(* end of [fingertree.sats] *)
