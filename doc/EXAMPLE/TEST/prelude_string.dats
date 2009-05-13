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
//
  val s1 = string1_of_string (s1)
  val s2 = string1_of_string (s2)
  val sgn = compare (s2, s1)
  val () = begin
    print "sgn(-1) = "; print sgn; print_newline ()
  end // end of [val]
//
  val s12 = s1 + s2
  val () = begin
    print "s12 (Hello, world!) = "; print s12; print_newline ()
  end // end of [val]
  val cs = string_explode (s12)
  val () = list_vt_free (cs)
//
  val cs = string_explode (s12)
  val s12' = string_implode (__cast cs) where {
    extern castfn __cast {n:nat} (cs: !list_vt (char, n)): list (char, n)
  } // end of [val]
  val () = begin
    print "s12' (Hello, world!) = "; print s12'; print_newline ()
  end // end of [val]
  val b = (s12 = s12')
  val () = begin
    print "b(true) = "; print b; print_newline ()
  end // end of [val]
  val () = list_vt_free (cs)
//
  val s12_upper = string_toupper (s12)
  val () = begin
    print "s12_upper (HELLO, WORLD!) = "; print s12_upper; print_newline ()
  end // end of [val]
  val s12_lower = string_tolower (s12)
  val () = begin
    print "s12_lower (hello, world!) = "; print s12_lower; print_newline ()
  end // end of [val]
//
  val ind = string_index_of_string ("abcdefghijklmnopqrstuvwsyz", "def")
  val ind = int1_of_ssize1 (ind)
  val () = begin
    print "ind (3) = "; print ind; print_newline ()
  end // end of [val]
  val ind = string_index_of_string ("abcdefghijklmnopqrstuvwsyz", "defhij")
  val ind = int1_of_ssize1 (ind)
  val () = begin
    print "ind (-1) = "; print ind; print_newline ()
  end // end of [val]
//
  prval pf = unit_v ()
  val () = string_foreach__main (pf | "Hello, world!", f, null) where {
    fn f (pf: !unit_v | c: char, _p: !ptr):<1> void = print (c)
  } // end of [val]
  val () = print_newline ()
  prval unit_v () = pf
in
  print "The run of [prelude_string.dats] is done successfully!\n"
end // end of [main]

(* ****** ****** *)

(* end of [prelude_string.dats] *)
