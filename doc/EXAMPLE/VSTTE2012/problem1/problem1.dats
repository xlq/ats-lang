(*
** VSTTE 2012 Verification Competition
** Problem 1
**
** All is done (VT1, VT2, VT3)
*)

(* ****** ****** *)
//
absview ba_v (l:addr, nf: int, nt: int) // array of nf f's and nt t's
//
viewdef fba_v (l:addr, n:int) = ba_v (l, n, 0) // array of n f's
viewdef tba_v (l:addr, n:int) = ba_v (l, 0, n) // array of n t's
//
(* ****** ****** *)

abst@ype bbool (i:int) = byte // bool values represented by a byte

(* ****** ****** *)

extern
fun bbool_istrue {i:two} (x: bbool i): bool (i==1)
extern
fun bbool_isfalse {i:two} (x: bbool i): bool (i==0)

extern
fun bbool_ptrget {l:addr}
  {i:two} (pf: !bbool i @ l | p: ptr l): bbool(i)
// end of [bbool_ptrget]

extern
fun swap
  {l1,l2:addr}
  {i1,i2:two} (
  pf1: !bbool i1 @ l1 >> bbool i2 @ l1
, pf2: !bbool i2 @ l2 >> bbool i1 @ l2
| p1: ptr l1, p2: ptr l2
) : void // end of [swap]

(* ****** ****** *)

extern
praxi ba_v_nil {l:addr} (): ba_v (l, 0, 0)

extern
praxi ba_v_cons
  {l:addr}
  {nf,nt:nat}
  {i:two} (
  pfat: bbool(i) @ l, pf: ba_v (l+1, nf, nt)
) : ba_v (l, nf+1-i, nt+i)

extern
praxi ba_v_snoc
  {l:addr}
  {nf,nt:nat}
  {i:two} (
  pf: ba_v (l, nf, nt), pfat: bbool(i) @ l+nf+nt
) : ba_v (l, nf+1-i, nt+i)

extern
praxi ba_v_unnil {l:addr} (pf: ba_v (l, 0, 0)): void

extern
praxi ba_v_uncons
  {l:addr}
  {nf,nt:nat | nf+nt > 0} (
  pf: ba_v (l, nf, nt)
) : [i:two | i <= nt; 1 <= nf+i] (bbool(i) @ l, ba_v (l+1, nf-1+i, nt-i))

extern
praxi ba_v_unsnoc
  {l:addr}
  {nf,nt:nat | nf+nt > 0} (
  pf: ba_v (l, nf, nt)
) : [i:two | i <= nt; 1 <= nf+i] (bbool(i) @ l+nf+nt-1, ba_v (l, nf-1+i, nt-i))

(* ****** ****** *)

extern
fun tws_unimpl {l:addr} {n1,nf,nt,n2:nat} (
  pf_l: fba_v (l, n1), pf_m: ba_v (l+n1, nf, nt), pf_r: tba_v (l+n1+nf+nt, n2)
| p: ptr l, i: int n1, j: int (n1+nf+nt)
) : (fba_v (l, n1+nf), tba_v (l+n1+nf, nt+n2) | void)

fun tws {l:addr} {n1,nf,nt,n2:nat} .<nf+nt>. (
  pf_l: fba_v (l, n1), pf_m: ba_v (l+n1, nf, nt), pf_r: tba_v (l+n1+nf+nt, n2)
| p: ptr l, i: int n1, j: int (n1+nf+nt)
) : (fba_v (l, n1+nf), tba_v (l+n1+nf, nt+n2) | void) =
  if i < j then let
    prval (pfat, pf_m) = ba_v_uncons (pf_m)
    val x_i = !(p+i)
  in
    if bbool_isfalse (x_i) then let
      prval pf_l = ba_v_snoc (pf_l, pfat)
    in
      tws {l} (pf_l, pf_m, pf_r | p, i+1, j)
    end else
      tws_1 (pf_l, pfat, pf_m, pf_r | p, i+1, j)
    // end of [if]
  end else let
    prval () = ba_v_unnil (pf_m)
  in
    (pf_l, pf_r | ())
  end // end of [if]
// end of [tws]

and tws_1 {l:addr} {n1,nf,nt,n2:nat} .<nf+nt>. (
  pf_l: fba_v (l, n1)
, pfat: bbool(1) @ l+n1
, pf_m: ba_v (l+n1+1, nf, nt), pf_r: tba_v (l+n1+1+nf+nt, n2)
| p: ptr l, i: int (n1+1), j: int (n1+1+nf+nt)
) : (fba_v (l, n1+nf), tba_v (l+n1+nf, nt+n2+1) | void) =
  if i < j then let
    prval (pfat2, pf_m) = ba_v_unsnoc (pf_m)
    val x_j = bbool_ptrget (pfat2 | p+j-1)
  in
    if bbool_istrue (x_j) then let
      prval pf_r = ba_v_cons (pfat2, pf_r)
    in
      tws_1 (pf_l, pfat, pf_m, pf_r | p, i, j-1)
    end else let
      val () = swap (pfat, pfat2 | p+i-1, p+j-1)
      prval pf_l = ba_v_snoc (pf_l, pfat)
      prval pf_r = ba_v_cons (pfat2, pf_r)
    in
      tws (pf_l, pf_m, pf_r | p, i, j-1)
    end
  end else let
    prval () = ba_v_unnil (pf_m)
    prval pf_r = ba_v_cons (pfat, pf_r)
  in
    (pf_l, pf_r | ())
  end // end of [if]
// end of [tws_1]

(* ****** ****** *)

(*
** The type assigned to [two_way_sort] indicates that
** it turns an array of [nf] f's and [nt] t's into two
** adjacent arrays: the front one contains [nf] f's and
** the rear one [nt] t's.
**
** Would this be enough to cover the VT3 (verification task 3)?
**
*)

fun two_way_sort
  {l:addr} {nf,nt:nat} (
  pf: ba_v (l, nf, nt) | p: ptr l, n: int(nf+nt)
) : (fba_v (l, nf), tba_v (l+nf, nt) | void) =
  tws (ba_v_nil (), pf, ba_v_nil () | p, 0, n)

(* ****** ****** *)

(* end of [problem.dats] *)
