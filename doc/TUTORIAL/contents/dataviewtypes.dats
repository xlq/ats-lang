//
//
// Author: Hongwei Xi (Septemeber, 2007)
//
// Programming singly-linked lists in ATS
//

(* ****** ****** *)

(*

// [list_vt] is declared to model singly-linked lists
dataviewtype list_vt (a:viewt@ype+, int) =
  | list_vt_nil (a, 0)
  | {n:nat} list_vt_cons (a, n+1) of (a, list_vt (a, n))

viewtypedef List_vt (a:viewt@ype) = [n:nat] list_vt (a, n)

*)

(* ****** ****** *)

#define nil list_vt_nil
#define cons list_vt_cons

(* ****** ****** *)

// An implementation of the length function on singly-linked lists
fn{a:viewt@ype}
  list_vt_length {n:nat} (xs0: !list_vt (a, n)): int n = let
  fun loop {i,j:nat} .< i >.
    (xs: !list_vt (a, i), j: int j): int (i+j) =
    case+ xs of
    | cons (_, !xs1) => begin
        let val n = loop (!xs1, j+1) in fold@ xs; n end
      end
    | nil () => (fold@ xs; j)
in
  loop (xs0, 0)
end // end of [list_vt_length]

(* ****** ****** *)

// An implementation of the append function on singly-linked lists
fun{a:viewt@ype} list_vt_append {m,n:nat}
  (xs0: &list_vt (a, m) >> list_vt (a, m+n), ys: list_vt (a, n)): void =
  case+ : (xs0: list_vt (a, m+n)) => xs0 of
  | cons (_, !xs) => (list_vt_append (!xs, ys); fold@ xs0)
  | ~nil () => (xs0 := ys)

(* ****** ****** *)

// An implementation of the reverse function on singly-linked lists
fn{a:viewt@ype} list_vt_reverse {n:nat} (xs: &list_vt (a, n)): void = let
  fun revapp {m,n:nat} .< m >.
    (xs: list_vt (a, m), ys: list_vt (a, n)): list_vt (a, m+n) =
    case+ xs of
    | cons (_, !xs1) => begin
        let val xs1_v = !xs1 in !xs1 := ys; fold@ xs; revapp (xs1_v, xs) end
      end
    | ~nil () => ys
in
  xs := revapp (xs, nil ())    
end // end of [list_vt_reverse]

(* ****** ****** *)

// An implementation of quicksort on singly-linked lists
fun{a:viewt@ype}
  list_vt_qsort {n:nat} .< n, 0 >.
   (lte: (!a, !a) -> bool, xs: list_vt (a, n)): list_vt (a, n) =
  case+ xs of
  | cons (!x1, !xs1) =>
    let val xs1_v = !xs1 in
      list_vt_par<a> (
        view@ (!x1), view@ (!xs1) | lte, xs, xs1, x1, xs1_v, nil (), nil ()
      )
    end
  | nil () => (fold@ xs; xs)

and // [list_vt_par] for partition
  list_vt_par {l0,l1:addr} {p,q,r:nat} .< p+q+r, p+1 >.
  (pf0: a @ l0, pf1: List_vt a? @ l1 |
   lte: (!a, !a) -> bool, node: list_vt_cons_unfold (l0, l1), node1: ptr l1,
   x0: ptr l0, xs: list_vt (a, p), l: list_vt (a, q), r: list_vt (a, r))
  : list_vt (a, p+q+r+1) = case+ xs of
  | cons (!x1, !xs1) => let
      val xs1_v = !xs1
    in
      if lte (!x1, !x0) then begin
        !xs1 := l; fold@ xs;
        list_vt_par<a> (pf0, pf1 | lte, node, node1, x0, xs1_v, xs, r)
      end else begin
        !xs1 := r; fold@ xs;
        list_vt_par<a> (pf0, pf1 | lte, node, node1, x0, xs1_v, l, xs)
      end // end of [if]
    end // end of [cons]
  | ~nil () => let
      var l = list_vt_qsort<a> (lte, l) and r = list_vt_qsort<a> (lte, r)
    in
      !node1 := r; fold@ node; r := node; list_vt_append<a> (l, r); l
    end // end of [nil]

(* ****** ****** *)

(* end of [dataviewtypes.dats] *)
