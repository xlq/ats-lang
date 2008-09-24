//
// A parallelized implementation of mergesort
//
// Time: March 2008
// Author: Hongwei Xi (* hwxi AT cs DOT bu DOT edu *)
//

(* ****** ****** *)

#if undefined (ARG_MERGESORT_MT_DATS) #then

absviewt@ype T

extern fun lte_T_T (x: !T, y: !T):<> bool
extern fun compare_T_T (x: !T, y: !T):<> Sgn

overload compare with compare_T_T
overload <= with lte_T_T

#endif // end of [undefined (ARG_MERGE_MT_DATS)]

(* ****** ****** *)

staload "libats/SATS/parallel.sats"

(* ****** ****** *)

fn merge_split_find {m:nat} {b:addr} .<m>.
  (pfb: !array_v (T, m, b) | B: ptr b, m: int m, x: &T):<> natLte (m) = let
  fun loop
    {lft,rgt: int | 0 <= lft; lft <= rgt+1; rgt+1 <= m}
    .<rgt-lft+1>.
    (pfb: !array_v (T, m, b) | lft: int lft, rgt: int rgt, x: &T)
    :<cloptr> natLte (m) = begin
    if lft <= rgt then let
      val mid = lft + nhalf (rgt - lft)
      val (pfy, pfb_pfy | y) = array_ptr_takeout_tsz {T} (pfb | B, mid, sizeof<T>)
      val sgn = compare (x, !y)
      prval () = pfb := pfb_pfy (pfy)    
    in
      case+ sgn of
      |  1 => loop (pfb | mid+1, rgt, x)
      | ~1 => loop (pfb | lft, mid-1, x)
      | _ (* 0 *) => mid
    end else begin
      lft // Note that it is [lft] instead of [rgt]
    end
  end // end of [loop]
in
  loop (pfb | 0, m-1, x)
end

(* ****** ****** *)

// all these simple functions should be inlined!

fn array_ptr_move_1 {r1,r2:addr} (
    pf1: !array_v (T, 1, r1) >> array_v (T?, 1, r1)
  , pf2: !array_v (T?, 1, r2) >> array_v (T, 1, r2)
  | R1: ptr r1, R2: ptr r2
  ) :<> void = let
  prval (pf11, pf12) = array_v_unsome {T} (pf1)
  prval (pf21, pf22) = array_v_unsome {T?} (pf2)
  prval () = array_v_unnone (pf12)
  prval () = array_v_unnone (pf22)
  val () = !R2 := !R1
in
  pf1 := array_v_some {T?} (pf11, array_v_none {T?} ());
  pf2 := array_v_some {T} (pf21, array_v_none {T} ());
end

//

fn array_ptr_move_out_1 {r:addr} (
    pf: !array_v (T, 1, r) >> array_v (T?, 1, r) | R: ptr r
  ) :<> T = let
  prval (pf1, pf2) = array_v_unsome {T} (pf)
  prval () = array_v_unnone (pf2)
  val x = !R
in
  pf := array_v_some {T?} (pf1, array_v_none {T?} ()); x
end

fn array_ptr_move_into_1 {r:addr} (
    pf: !array_v (T?, 1, r) >> array_v (T, 1, r) | R: ptr r, x: T
  ) :<> void = let
  prval (pf1, pf2) = array_v_unsome {T?} (pf)
  prval () = array_v_unnone (pf2)
  val () = !R := x
in
  pf := array_v_some {T} (pf1, array_v_none {T} ())
end

//

fn array_ptr_move_into_2 {r:addr} (
    pf: !array_v (T?, 2, r) >> array_v (T, 2, r) | R: ptr r, x1: T, x2: T
  ) :<> void = let
  prval (pf1, pf2) = array_v_unsome {T?} (pf)
  val () = !R := x1
  val () = array_ptr_move_into_1 (pf2 | R+sizeof<T>, x2)
in
  pf := array_v_some {T} (pf1, pf2)
end

(* ****** ****** *)
  
fun merge {l:pos;m:nat} {a,b,c:addr} .<l+m,1>. (
    pfa: !array_v (T, l, a) >> array_v (T?, l, a)
  , pfb: !array_v (T, m, b) >> array_v (T?, m, b)
  , pfc: !array_v (T?, l+m, c) >> array_v (T, l+m, c)
  | A: ptr a, l: int l
  , B: ptr b, m: int m
  , C: ptr c
  ) :<1> void = begin
  if l >= m then begin
    merge_gte (pfa, pfb, pfc | A, l, B, m, C)
  end else begin
    merge_gte (pfb, pfa, pfc | B, m, A, l, C)
  end
end // end of [merge]

and merge_gte
  {l:pos;m:nat; l >= m} {a,b,c:addr} .<l+m,0>. (
    pfa: !array_v (T, l, a) >> array_v (T?, l, a)
  , pfb: !array_v (T, m, b) >> array_v (T?, m, b)
  , pfc: !array_v (T?, l+m, c) >> array_v (T, l+m, c)
  | A: ptr a, l: int l
  , B: ptr b, m: int m
  , C: ptr c
  ) :<1> void = begin
  case+ l of
  | 1 => begin case+ m of
    | 0 => let
        prval () = array_v_unnone (pfb)
        prval () = (pfb := array_v_none {T?} ())
        val x = array_ptr_move_out_1 (pfa | A)
      in
        array_ptr_move_into_1 (pfc | C, x)
      end
    | _ (* m = 1 *) =>> let
        val x = array_ptr_move_out_1 (pfa | A)
        val y = array_ptr_move_out_1 (pfb | B)
      in
        if x <= y then begin
          array_ptr_move_into_2 (pfc | C, x, y)
        end else begin
          array_ptr_move_into_2 (pfc | C, y, x)
        end
      end // end of [_]
    end // end of [l = 1]
  | _ (* >1 *) =>> let
      val [l2:int] l2 = nhalf (l)
      val (pfx, pfa_pfx | x) = array_ptr_takeout_tsz {T} (pfa | A, l2, sizeof<T>)
      val [m2:int] m2 = merge_split_find (pfb | B, m, !x)
      prval () = pfa := pfa_pfx (pfx)
      val [a_ofs:int] (pfa_mul | A_ofs) = l2 imul2 sizeof<T>
      prval pfa1_mul = mul_commute (pfa_mul)
      val [b_ofs:int] (pfb_mul | B_ofs) = m2 imul2 sizeof<T>
      prval pfb1_mul = mul_commute (pfb_mul)
      prval pfc1_mul = mul_distribute (pfa1_mul, pfb1_mul)
      prval pfc_mul = mul_commute (pfc1_mul)
      val C_ofs = A_ofs + B_ofs
      prval (pfa1, pfa2) = array_v_split {T} {l,l2} (pfa_mul, pfa)
      prval (pfb1, pfb2) = array_v_split {T} {m,m2} (pfb_mul, pfb)
      prval (pfc1, pfc2) = array_v_split {T?} {l+m,l2+m2} (pfc_mul, pfc)
      val ll2 = l - l2 and mm2 = m - m2

      val // par
          () = merge (pfa1, pfb1, pfc1 | A, l2, B, m2, C)
      and 
          () = merge (pfa2, pfb2, pfc2 | A+A_ofs, ll2, B+B_ofs, mm2, C+C_ofs)
    in
      pfa := array_v_unsplit {T?} {l2,l-l2} (pfa_mul, pfa1, pfa2);
      pfb := array_v_unsplit {T?} {m2,m-m2} (pfb_mul, pfb1, pfb2);
      pfc := array_v_unsplit {T} {l2+m2,l-l2+m-m2} (pfc_mul, pfc1, pfc2);
    end
end // end of [merge_gte]

(* ****** ****** *)

#define CUTOFF 1024

fun mergesort1 {l:nat} {a1,a2:addr} .<l>. (
    pfa1: !array_v (T, l, a1)
  , pfa2: !array_v (T?, l, a2)
  | A1: ptr a1, A2: ptr a2, l: int l
  ) :<1> void = begin
  if l >= 2 then let
    val [l2:int] l2= nhalf (l); val ll2 = l - l2
    val [ofs:int] (pfa_mul | ofs) = l2 imul2 sizeof<T>
    prval (pfa11, pfa12) = array_v_split {T} {l,l2} (pfa_mul, pfa1)
    prval (pfa21, pfa22) = array_v_split {T?} {l,l2} (pfa_mul, pfa2)
    val ll2 = l - l2

    val () =
      if :(
        pfa11: array_v (T?, l2, a1)
      , pfa12: array_v (T?, l-l2, a1+ofs)
      , pfa21: array_v (T, l2, a2)
      , pfa22: array_v (T, l-l2, a2+ofs)
      ) => l2 >= CUTOFF then let
        val par
            () = mergesort2 (pfa11, pfa21 | A1, A2, l2)
        and 
            () = mergesort2 (pfa12, pfa22 | A1+ofs, A2+ofs, ll2)
      in
        // empty
      end else let
        val () = mergesort2 (pfa11, pfa21 | A1, A2, l2)
        and () = mergesort2 (pfa12, pfa22 | A1+ofs, A2+ofs, ll2)
      in
        // empty
      end

    prval () = begin
      pfa1 := array_v_unsplit {T?} {l2,l-l2} (pfa_mul, pfa11, pfa12)
    end
    val () = merge (pfa21, pfa22, pfa1 | A2, l2, A2+ofs, ll2, A1)
  in
    pfa2 := array_v_unsplit {T?} {l2,l-l2} (pfa_mul, pfa21, pfa22)
  end
end // end of [mergesort1]

and mergesort2 {l:pos} {a1,a2:addr} .<l>. (
    pfa1: !array_v (T, l, a1) >> array_v (T?, l, a1)
  , pfa2: !array_v (T?, l, a2) >> array_v (T, l, a2)
  | A1: ptr a1, A2: ptr a2, l: int l
  ) :<1> void = begin
  if l >= 2 then let
    val [l2:int] l2= nhalf (l); val ll2 = l - l2
    val [ofs:int] (pfa_mul | ofs) = l2 imul2 sizeof<T>
    prval (pfa11, pfa12) = array_v_split {T} {l,l2} (pfa_mul, pfa1)
    prval (pfa21, pfa22) = array_v_split {T?} {l,l2} (pfa_mul, pfa2)
    val ll2 = l - l2

    val () =
      if :(
        pfa11: array_v (T, l2, a1)
      , pfa12: array_v (T, l-l2, a1+ofs)
      , pfa21: array_v (T?, l2, a2)
      , pfa22: array_v (T?, l-l2, a2+ofs)
      ) => l2 >= CUTOFF then let
        val par
          () = mergesort1 (pfa11, pfa21 | A1, A2, l2)
        and 
          () = mergesort1 (pfa12, pfa22 | A1+ofs, A2+ofs, ll2)
      in
        // empty
      end else let
        val
          () = mergesort1 (pfa11, pfa21 | A1, A2, l2)
        and 
          () = mergesort1 (pfa12, pfa22 | A1+ofs, A2+ofs, ll2)
      in
        // empty
      end

    prval () = begin
      pfa2 := array_v_unsplit {T?} {l2,l-l2} (pfa_mul, pfa21, pfa22);
    end
    val () = merge (pfa11, pfa12, pfa2 | A1, l2, A1+ofs, ll2, A2)
  in
    pfa1 := array_v_unsplit {T?} {l2,l-l2} (pfa_mul, pfa11, pfa12)
  end else begin // l = 1
    array_ptr_move_1 (pfa1, pfa2 | A1, A2)
  end
end // end of [mergesort2]

(* ****** ****** *)

extern fun mergesort {l:nat} {a:addr}
  (pfa: !array_v (T, l, a) | A: ptr a, l: int l): void

implement mergesort (pfa1 | A1, l) = let
  val (pf_gc, pfa2 | A2) = array_ptr_alloc_tsz {T} (l, sizeof<T>)
  val () = mergesort1 (pfa1, pfa2 | A1, A2, l)
  val () = array_ptr_free {T} (pf_gc, pfa2 | A2)
in
  // empty
end // end of [mergesort]

(* ****** ****** *)

(* end of [mergesort_mt.dats] *)
