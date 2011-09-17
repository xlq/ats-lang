(*
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Start Time: September 16, 2011
*)

(*
** HX: ATS/Anairiats cannot handle this one.
** HX: Hopefully, ATS/Postiats will be able to handle it.
*)

extern
prfun SMI {P:int->prop}
  (fpf: {n:nat} ({k:nat | k < n} P(k)) -<prf> P(n)): {n:nat} P(n)
// end of [SMI]

extern praxi allprop {P:prop | false} (): P

implement
SMI {P} (fpf) {n} = let
  propdef Q
    (n:int) = {k:nat | k <= n} P (k)
  prfun lemma
    {n:nat} .<n>. (): Q (n) = lam {k:nat | k <= n} =>
    sif n > 0 then let
      val IH = lemma {n-1} ()
    in
      sif k < n then IH {k} else fpf {n} (IH)
    end else
      fpf {0} (lam => allprop ())
    (* end of [sif] *)
  // end o [lemma]
in
  lemma {n} () {n}
end // end of [SMI]

(* end of [SMI] *)
