(*
**
** A proof of the equivalence of two definitions
** of the Ackermann function
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December 2, 2009
**
*)

(* ****** ****** *)

(*

The following two functions are proven to be the same
(in the set-theoretic sense):

fun ack
  (m:int, n:int): int =
  case+ m of
  | 0 => n+1
  | _ => begin case+ n of
    | 0 => ack (m-1, 1) | _ => ack (m-1, ack (m, n-1))
    end // end of [_]
// end of [ack1]

fun ackf (m: int): int -<cloref1> int = let
  fun helper
    (f: int -<cloref1> int): int -<cloref1> int =
    lam n => if n = 0 then f (1) else f (helper f (n-1))
  // end of [helper]
in
  case+ m of
  | 0 => lam n => n+1 | _ => helper (ackf (m-1))
end // end of [ackf]

*)

(* ****** ****** *)

dataprop ACK (int, int, int) =
  | {n:nat} ACK1 (0, n, n+1) of ()
  | {m:nat} {r:int} ACK2 (m+1, 0, r) of ACK (m, 1, r)
  | {m,n:nat} {r1,r2:int}
    ACK3 (m+1, n+1, r2) of (ACK (m+1, n, r1), ACK (m, r1, r2))
// end of [ACK]

prfun ack_nat_nat_nat {m,n:nat}
  {r:int} .<m,n>. (pf: ACK (m, n, r)): [r >= 0] void =
  case+ pf of
  | ACK1 () => ()
  | ACK2 pf1 => ack_nat_nat_nat (pf1)
  | ACK3 (pf1, pf2) => let
      prval () = ack_nat_nat_nat pf1
      prval () = ack_nat_nat_nat pf2
    in
      // nothing
    end // end of [ACK3]
// end of [ack_nat_nat_nat]

sortdef int2rel = (int, int) -> prop

dataprop SUCC (int, int) = {n:nat} SUCC1 (n, n+1) of ()

dataprop HELPER (rel:int2rel, int, int) =
  | {r:int} HELPER1 (rel, 0, r) of rel (1, r)
  | {n:nat} {r1,r2:int}
    HELPER2 (rel, n+1, r2) of (HELPER (rel, n, r1), rel (r1, r2))
// end of [HELPER]

dataprop ACKF (int, int2rel) =
  | ACKF1 (0, SUCC) of ()
  | {m:nat} {rel:int2rel}
    ACKF2 (
      m+1, lam (r1:int, r2:int) => HELPER (rel, r1, r2)) of ACKF (m, rel
    ) // end of [ACKF2]
// end of [ACKF]

prfun ACKF_istot
  {m:nat} .<m>. (): [rel:int2rel] ACKF (m, rel) =
  sif m > 0 then ACKF2 (ACKF_istot {m-1} ()) else ACKF1 ()
// end of [ACKF_istot]

(*
** this lemma means that applying ackf (m) to n gives
** ack (m, n)
*)
prfun ackf_ack_lemma1
  {m,n:nat} {rel:int2rel} {r:int} .<m,n+1>.
  (pf1: ACKF (m, rel), pf2: rel (n, r)): ACK (m, n, r) =
  case pf1 of
  | ACKF1 () => let
      prval SUCC1 () = pf2 in ACK1 {n} ()
    end // end of [ACKF1]
  | ACKF2 pf11 => ackf_ack_lemma2 (pf11, pf2)
// end of [ackf_ack_lemma1]

(*
** this lemma means that applying ackf (m) n times to 1 
** gives ack (m+1, n)
*)
and ackf_ack_lemma2
  {m,n:nat} {rel:int2rel} {r:int} .<m+1,n>.
  (pf1: ACKF (m, rel), pf2: HELPER (rel, n, r)): ACK (m+1, n, r) =
  sif n > 0 then let
    prval HELPER2 (pf21, pf22) = pf2
    prval pf_ack = ackf_ack_lemma2 (pf1, pf21) // ACK (m+1, n-1)
    prval () = ack_nat_nat_nat (pf_ack)
  in
    ACK3 (pf_ack, ackf_ack_lemma1 (pf1, pf22))
  end else let // n == 0
    prval HELPER1 (pf21) = pf2
  in
    ACK2 (ackf_ack_lemma1 (pf1, pf21))
  end // end of [sif]
// end of [ackf_ack_lemma2]

(* ****** ****** *)

(* end of [Ackermann.dats] *)
