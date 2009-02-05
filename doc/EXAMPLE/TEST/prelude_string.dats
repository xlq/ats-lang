//
// some testing code for functions declared in
// prelude/SATS/string.sats
//

(* ****** ****** *)

// staload "prelude/SATS/string.sats"

(* ****** ****** *)

staload "prelude/DATS/list_vt.dats"

(* ****** ****** *)

implement main (argc, argv) = let
  val s1 = "Hello"
  val s2 = ", world!"
  val sgn = compare (s1, s2)
  val () = begin
    print "sgn(1) = "; print sgn; print_newline ()
  end // end of [val]
  val s12 = s1 + s2
  val () = begin
    print "s12 (Hello, world!) = "; print s12; print_newline ()
  end // end of [val]

  val s1 = string1_of_string (s1)
  val s2 = string1_of_string (s2)
  val sgn = compare (s2, s1)
  val () = begin
    print "sgn(-1) = "; print sgn; print_newline ()
  end // end of [val]

  val s12 = s1 + s2
  val () = begin
    print "s12 (Hello, world!) = "; print s12; print_newline ()
  end // end of [val]
  val cs = string_explode (s12)
  val () = list_vt_free (cs)

  val cs = let
    val (vbox pf | p12) = strbuf_of_string1 (s12)
  in
    strbuf_explode (!p12)
  end
  val cs = list_of_list_vt (cs)
  val s12' = string_implode (cs)
  val () = begin
    print "s12' (Hello, world!) = "; print s12'; print_newline ()
  end // end of [val]
  val b = (s12 = s12')
  val () = begin
    print "b(true) = "; print b; print_newline ()
  end // end of [val]

  val s12_upper = string_toupper (s12)
  val () = begin
    print "s12_upper (HELLO, WORLD!) = "; print s12_upper; print_newline ()
  end // end of [val]
  val s12_lower = string_tolower (s12)
  val () = begin
    print "s12_lower (hello, world!) = "; print s12_lower; print_newline ()
  end // end of [val]
in
  print "The run of [prelude_string.dats] is done successfully!\n"
end // end of [main]

(* ****** ****** *)

(* end of [prelude_string.dats] *)
