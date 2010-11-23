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

#define ATS_DYNLOADFLAG 0 // no dynamic loading at run-time

(* ****** ****** *)

staload "contrib/Fingertree/SATS/fingertree.sats"

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

typedef ft0node = ftnode (void, 0, 0)

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

(* ****** ****** *)

prfun
ftnode_prop_szpos {a:t@ype}
  {d:int} {n:int} .<max(d,0)>.
  (xn: ftnode (a, d, n)): [n > 0] void =
  case+ xn of
  | FTN1 _ => ()
  | FTN2 (xn1, xn2) => {
      val () = ftnode_prop_szpos (xn1)
    } // end of [FTN2]
  | FTN3 (xn1, xn2, xn3) => {
      val () = ftnode_prop_szpos (xn1)
    } // end of [FTN3]
// end of [ftnode_prop_szpos]

(* ****** ****** *)

prfun
ftdigit_prop_szpos {a:t@ype}
  {d:int} {n:int} .<>.
  (xd: ftdigit (a, d, n)): [n > 0] void =
  case+ xd of
  | FTD1 (xn1) => ftnode_prop_szpos (xn1)
  | FTD2 (xn1, _) => ftnode_prop_szpos (xn1)
  | FTD3 (xn1, _, _) => ftnode_prop_szpos (xn1)
  | FTD4 (xn1, _, _, _) => ftnode_prop_szpos (xn1)
// end of [ftdigit_prop_szpos]

(* ****** ****** *)

prfun
fingertree_prop1_sznat
  {a:t@ype}
  {d:int} {n:int} .<>.
  (xt: fingertree (a, d, n)): [n >= 0] void =
  case+ xt of
  | FTempty () => ()
  | FTsingle (xn) => ftnode_prop_szpos (xn)
  | FTdeep (pr, m, sf) => {
      val () = ftdigit_prop_szpos (pr) and () = ftdigit_prop_szpos (sf)
    } // end of [FTdeep]
// end of [fingertree_prop1_sznat]

(* ****** ****** *)

fun
ftnode_size
  {a:t@ype}
  {d:int}
  {n:nat} .<n>. (
  xn: ftnode (a, d, n)
) :<> int n = let
  macdef nsz (xn) = ftnode_size ,(xn)
in
  case+ xn of
  | FTN1 _ => 1
  | FTN2 (xn1, xn2) => let
      prval () = ftnode_prop_szpos (xn1)
      prval () = ftnode_prop_szpos (xn2)
    in
      nsz (xn1) + nsz (xn2)
    end // end of [FTN2]
  | FTN3 (xn1, xn2, xn3) => let
      prval () = ftnode_prop_szpos (xn1)
      prval () = ftnode_prop_szpos (xn2)
      prval () = ftnode_prop_szpos (xn3)
    in
      nsz (xn1) + nsz (xn2) + nsz (xn3)
    end // endof [FTN3]
end // end of [ftnode_size]

(* ****** ****** *)

fun
ftdigit_size
  {a:t@ype}
  {d:int}
  {n:int} .<>. (
  xd: ftdigit (a, d, n)
) :<> int n = let
  macdef nsz (x) = ftnode_size ,(x)
in
  case+ xd of
  | FTD1 (xn1) => nsz (xn1)
  | FTD2 (xn1, xn2) => nsz (xn1) + nsz (xn2)
  | FTD3 (xn1, xn2, xn3) => nsz (xn1) + nsz (xn2) + nsz (xn3)
  | FTD4 (xn1, xn2, xn3, xn4) => nsz (xn1) + nsz (xn2) + nsz (xn3) + nsz (xn4)
end // end of [ftdigit_size]

(* ****** ****** *)

fun ftnode2ftdigit
  {a:t@ype} {d:pos} {n:int} .<>.
  (xn: ftnode (a, d, n)):<> ftdigit (a, d-1, n) =
  case+ xn of
  | FTN2 (xn1, xn2) => FTD2 (xn1, xn2)
  | FTN3 (xn1, xn2, xn3) => FTD3 (xn1, xn2, xn3)
// end of [ftnode2ftdigit]

(* ****** ****** *)

fun ftdigit2fingertree
  {a:t@ype} {d:nat} {n:int} .<>.
  (xd: ftdigit (a, d, n)):<> fingertree (a, d, n) =
  case+ xd of
  | FTD1 (xn1) => FTsingle (xn1)
  | FTD2 (xn1, xn2) => FTdeep (FTD1 (xn1), FTempty(), FTD1 (xn2))
  | FTD3 (xn1, xn2, xn3) => FTdeep (FTD2 (xn1, xn2), FTempty(), FTD1 (xn3))
  | FTD4 (xn1, xn2, xn3, xn4) => FTdeep (FTD2 (xn1, xn2), FTempty(), FTD2 (xn3, xn4))
// end of [ftdigit2fingertree]

(* ****** ****** *)

extern
fun fingertree_cons
  {a:t@ype} {d:nat} {n1,n2:int} (
  xn: ftnode (a, d, n1), xt: fingertree (a, d, n2)
) :<> fingertree (a, d, n1+n2) // end of [fingertree_cons]

implement
fingertree_cons{a}
  (xn, xt) = cons (xn, xt) where {
//
fun cons {d:nat}
  {n1,n2:int | n2 >= 0} .<n2>. (
  xn: ftnode (a, d, n1), xt: fingertree (a, d, n2)
) :<> fingertree (a, d, n1+n2) = let
  prval () = ftnode_prop_szpos (xn) in
  case+ xt of
  | FTempty () => FTsingle (xn)
  | FTsingle (xn1) => let
      prval () = ftnode_prop_szpos (xn1)
    in
      FTdeep (FTD1(xn), FTempty(), FTD1(xn1))
    end // end [FTsingle]
  | FTdeep (pr, m, sf) => (case+ pr of
    | FTD1 (xn1) => FTdeep (FTD2 (xn, xn1), m, sf) 
    | FTD2 (xn1, xn2) => FTdeep (FTD3 (xn, xn1, xn2), m, sf)
    | FTD3 (xn1, xn2, xn3) => FTdeep (FTD4 (xn, xn1, xn2, xn3), m, sf)
    | FTD4 (xn1, xn2, xn3, xn4) => let
        val pr = FTD2 (xn, xn1)
//
        prval () = ftdigit_prop_szpos (sf)
        prval () = fingertree_prop1_sznat (m)
//
        val m = cons (FTN3 (xn2, xn3, xn4), m)
      in
        FTdeep (pr, m, sf)
      end // end of [FTD4]
    ) // end of [FTdeep]
end // end of [cons]
//
prval () = fingertree_prop1_sznat (xt)
//
} // end of [fingertree_cons]

(* ****** ****** *)

extern
fun fingertree_uncons
  {a:t@ype} {d:nat} {n:pos} (
  xt: fingertree (a, d, n), r: &ftnode? >> ftnode (a, d, n1)
) :<> #[n1:nat] fingertree (a, d, n-n1)
// end of [fingertree_uncons]

implement
fingertree_uncons{a}
  (xt, r) = uncons (xt, r) where {
//
fun uncons {d:nat} {n:pos} .<n>. (
  xt: fingertree (a, d, n), r: &ft0node? >> ftnode (a, d, n1)
) :<> #[n1:nat | n1 <= n] fingertree (a, d, n-n1) =
  case+ xt of
  | FTsingle (xn) => let
      val () = r := xn in FTempty ()
    end // end of [Single]
  | FTdeep (pr, m, sf) => (case+ pr of
    | FTD1 (xn) => let
        val () = r := xn
        prval () = ftdigit_prop_szpos (pr)
        prval () = ftdigit_prop_szpos (sf)
      in
        case+ m of
        | FTempty () => ftdigit2fingertree (sf)
        | FTsingle (xn1) => FTdeep (ftnode2ftdigit (xn1), FTempty (), sf)
        | FTdeep (pr1, m1, sf1) => let
            var r1: ft0node?
            prval () = ftdigit_prop_szpos (pr1)
            prval () = fingertree_prop1_sznat (m1)
            prval () = ftdigit_prop_szpos (sf1)
            val m = uncons (m, r1)
          in
            FTdeep (ftnode2ftdigit (r1), m, sf)
          end // end of [_]
      end // end of [FTD1]
    | FTD2 (xn, xn1) => let
        val () = r := xn in FTdeep (FTD1 (xn1), m, sf)
      end // end of [FTD2]
    | FTD3 (xn, xn1, xn2) => let
        val () = r := xn in FTdeep (FTD2 (xn1, xn2), m, sf)
      end // end of [FTD3]
    | FTD4 (xn, xn1, xn2, xn3) => let
        val () = r := xn in FTdeep (FTD3 (xn1, xn2, xn3), m, sf)
      end // end of [FTD4]
    ) // end of [FTdeep]
// end of [uncons]
} // end of [fingertree_uncons]

(* ****** ****** *)

extern
fun fingertree_snoc
  {a:t@ype} {d:nat} {n1,n2:int} (
  xn: ftnode (a, d, n1), xt: fingertree (a, d, n2)
) :<> fingertree (a, d, n1+n2) // end of [fingertree_snoc]

implement
fingertree_snoc{a}
  (xn, xt) = snoc (xn, xt) where {
//
fun snoc {d:nat}
  {n1,n2:int | n2 >= 0} .<n2>. (
  xn: ftnode (a, d, n1), xt: fingertree (a, d, n2)
) :<> fingertree (a, d, n1+n2) = let
  prval () = ftnode_prop_szpos (xn) in
  case+ xt of
  | FTempty () => FTsingle (xn)
  | FTsingle (xn1) => let
      prval () = ftnode_prop_szpos (xn1)
    in
      FTdeep (FTD1(xn1), FTempty(), FTD1(xn))
    end // end [FTsingle]
  | FTdeep (pr, m, sf) => (case+ sf of
    | FTD1 (xn1) => FTdeep (pr, m, FTD2 (xn1, xn))
    | FTD2 (xn1, xn2) => FTdeep (pr, m, FTD3 (xn1, xn2, xn))
    | FTD3 (xn1, xn2, xn3) => FTdeep (pr, m, FTD4 (xn1, xn2, xn3, xn))
    | FTD4 (xn1, xn2, xn3, xn4) => let
        val sf = FTD2 (xn4, xn)
//
        prval () = ftdigit_prop_szpos (pr)
        prval () = fingertree_prop1_sznat (m)
//
        val m = snoc (FTN3 (xn1, xn2, xn3), m)
      in
        FTdeep (pr, m, sf)
      end // end of [FTD4]
    ) // end of [FTdeep]
end // end of [snoc]
//
prval () = fingertree_prop1_sznat (xt)
//
} // end of [fingertree_snoc]

(* ****** ****** *)

assume tree_t0ype_int_type
  (a:t@ype, n:int) = fingertree (a, 0, n)
// end of [tree_t0ype_int]

(* ****** ****** *)

implement{}
tree_nil () = FTempty ()

implement{}
tree_is_nil (xt) =
  case+ xt of
  | FTempty () => true
  | FTsingle (xn) => let
      prval () = ftnode_prop_szpos (xn) in false
    end // end of [FTsingle]
  | FTdeep (pr, _, _) => let
      prval () = ftdigit_prop_szpos (pr) in false
    end // end of [FTdeep]
// end of [tree_is_nil]

(* ****** ****** *)

extern
fun fingertree_unsnoc
  {a:t@ype} {d:nat} {n:pos} (
  xt: fingertree (a, d, n), r: &ftnode? >> ftnode (a, d, n1)
) :<> #[n1:nat] fingertree (a, d, n-n1)
// end of [fingertree_unsnoc]

implement
fingertree_unsnoc{a}
  (xt, r) = unsnoc (xt, r) where {
//
fun unsnoc {d:nat} {n:pos} .<n>. (
  xt: fingertree (a, d, n), r: &ft0node? >> ftnode (a, d, n1)
) :<> #[n1:nat | n1 <= n] fingertree (a, d, n-n1) =
  case+ xt of
  | FTsingle (xn) => let
      val () = r := xn in FTempty ()
    end // end of [Single]
  | FTdeep (pr, m, sf) => (case+ sf of
    | FTD1 (xn) => let
        val () = r := xn
        prval () = ftdigit_prop_szpos (pr)
        prval () = ftdigit_prop_szpos (sf)
      in
        case+ m of
        | FTempty () => ftdigit2fingertree (pr)
        | FTsingle (xn1) => FTdeep (pr, FTempty (), ftnode2ftdigit (xn1))
        | FTdeep (pr1, m1, sf1) => let
            var r1: ft0node?
            prval () = ftdigit_prop_szpos (pr1)
            prval () = fingertree_prop1_sznat (m1)
            prval () = ftdigit_prop_szpos (sf1)
            val m = unsnoc (m, r1)
          in
            FTdeep (pr, m, ftnode2ftdigit (r1))
          end // end of [_]
      end // end of [FTD1]
    | FTD2 (xn1, xn) => let
        val () = r := xn in FTdeep (pr, m, FTD1 (xn1))
      end // end of [FTD2]
    | FTD3 (xn1, xn2, xn) => let
        val () = r := xn in FTdeep (pr, m, FTD2 (xn1, xn2))
      end // end of [FTD3]
    | FTD4 (xn1, xn2, xn3, xn) => let
        val () = r := xn in FTdeep (pr, m, FTD3 (xn1, xn2, xn3))
      end // end of [FTD4]
    ) // end of [FTdeep]
// end of [unsnoc]
} // end of [fingertree_unsnoc]

(* ****** ****** *)

implement{a}
tree_cons (xn, xt) =
  fingertree_cons (FTN1 (xn), xt)
// end of [tree_cons]

implement{a}
tree_uncons
  (xt, r) = xt where {
  var xn: ft0node?
  val xt = fingertree_uncons (xt, xn)
  val+ FTN1 (x) = xn
  val () = (r := x)
} // end of [tree_uncons]

(* ****** ****** *)

implement{a}
tree_snoc (xn, xt) =
  fingertree_snoc (FTN1 (xn), xt)
// end of [tree_snoc]

implement{a}
tree_unsnoc
  (xt, r) = xt where {
  var xn: ft0node?
  val xt = fingertree_unsnoc (xt, xn)
  val+ FTN1 (x) = xn
  val () = (r := x)
} // end of [tree_unsnoc]

(* ****** ****** *)

(* end of [fingertree.dats] *)
