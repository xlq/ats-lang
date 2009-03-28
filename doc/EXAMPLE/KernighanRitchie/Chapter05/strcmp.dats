//
// K&R, 2nd edition, page 106
//

// Translated to ATS by Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(*

int strcmp (char *s, char *t) {
  int i;
  for (i = 0; s[i] == t[i]; ++i) if (!s[i]) return 0 ;
  return s[i] - t[i] ;
}

*)

extern fun strcmp
  {m1,n1:nat | n1 < m1}
  {m2,n2:nat | n2 < m2} (
    s1: &strbuf (m1, n1), s2: &strbuf (m2, n2)
  ) :<> Sgn

implement strcmp {m1,n1} {m2,n2}
  (s1, s2) = loop (s1, s2, 0) where {
  fun loop {i:nat | i <= n1; i <= n2} .<n1-i>.
    (s1: &strbuf (m1, n1), s2: &strbuf (m2, n2), i: size_t i):<> Sgn =
    if strbuf_is_at_end (s1, i) then begin
      if strbuf_is_at_end (s2, i) then 0 else ~1
    end else begin
      if strbuf_is_at_end (s2, i) then 1 else let
        val sgn = compare (s1[i], s2[i])
      in
        if (sgn = 0) then loop (s1, s2, i+1) else sgn
      end // end of [if]
    end // end of [if]
} // end of [strcmp]

(* ****** ****** *)

implement main (argc, argv) = let
  val () = assert (argc >= 3)
  val str1 = string1_of_string (argv.[1])
  and str2 = string1_of_string (argv.[2])
  val sgn = let
    val (vbox pf1_buf | p1_buf) = strbuf1_of_string1 str1
  in
    $effmask_all let
      val (vbox pf2_buf | p2_buf) = strbuf1_of_string1 str2
    in
      strcmp (!p1_buf, !p2_buf)
    end // end of [let]
  end // end of [val]
in
  printf ("strcmp (%s, %s) = %i\n", @(str1, str2, sgn))
end // end of [main]

(* ****** ****** *)

(* end of [strcmp.dats] *)
