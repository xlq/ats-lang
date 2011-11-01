(*
** HX-2011-11-01: first-order propositional logic
*)

absprop PBOT ()
absprop POR (prop, prop)
absprop PAND (prop, prop)
absprop PIMP (prop, prop)
absprop PNEG (prop)

extern
praxi and_intr {A,B:prop} (pf1: A, pf2: B): PAND (A, B)
extern
praxi and_elim_l {A,B:prop} (pf: PAND (A, B)): A
extern
praxi and_elim_r {A,B:prop} (pf: PAND (A, B)): B

extern
praxi or_intr_l {A,B:prop} (pf: A): POR (A, B)
extern
praxi or_intr_r {A,B:prop} (pf: B): POR (A, B)
extern
praxi or_elim {A,B:prop} {C:prop}
  (pf1: A -> C, pf2: B -> C, pf3: POR (A, B)): C

extern
praxi imp_intr {A,B:prop} (pf: A -> B): PIMP (A, B)
extern
praxi imp_elim {A,B:prop} (pf1: PIMP (A, B), pf2: A): B

extern
praxi neg_intr {A:prop} (pf: A -> PBOT()): PNEG (A)
extern
praxi neg_elim {A:prop} (pf1: PNEG(A), pf2: A): PBOT()

extern
praxi negneg_elim {A:prop} (pf: PNEG(PNEG(A))): A

(* ****** ****** *)

prfn and_commute
  {A,B:prop} (
  pf: PAND (A, B)
) : PAND (B, A) = let
  val pf_A = and_elim_l (pf)
  val pf_B = and_elim_r (pf)
in
  and_intr (pf_B, pf_A)
end // end of [lemma1]

prfn or_commute
  {A,B:prop} (
  pf: POR (A, B)
) : POR (B, A) = let
  val pf1 = lam (x: A): POR (B, A) =<prf> or_intr_r (x)
  val pf2 = lam (x: B): POR (B, A) =<prf> or_intr_l (x)
in
  or_elim (pf1, pf2, pf)
end // end of [lemma1]

(* ****** ****** *)

(* prop-fstord.dats *)
