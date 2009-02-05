//
// some testing code for functions declared in
// libats/SATS/intinf.sats
//

(* ****** ****** *)

staload "libats/SATS/regexp.sats"

(* ****** ****** *)

fn prerr_usage (cmd: string): void =
  prerrf ("Usage: %s <integer>\n", @(cmd))
// end of [prerr_usage]

(* ****** ****** *)

dynload "libats/DATS/regexp.dats"

(* ****** ****** *)

implement main (argc, argv) = let
  val () = if (argc <> 2) then prerr_usage (argv.[0])
  val intpat = "^[1-9][0-9]*$"
  val () = assert (argc = 2)
  val intstr = argv.[1]
  val (pf_gc, pf_at | p_re) = regexp_compile_exn intpat
  val ans = test_regexp_match_str (!p_re, intstr)
  val () = regexp_free (pf_gc, pf_at | p_re)
in
  print "ans = "; print ans; print_newline ()
end // end of [main]

(* ****** ****** *)

(* end of [libats_intinf.dats] *)
