(*
//
// Some code for testing the Enigma simulator
//
*)

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

staload "libc/SATS/random.sats"

(* ****** ****** *)

staload "enigma.sats"

(* ****** ****** *)

dynload "enigma.dats"

(* ****** ****** *)

implement
main () = {
//
#define nil list_nil
#define :: list_cons
//
  // val () = srand48 (1000000L)
  val () = srand48_with_time ()
//
  val E = enigma_make_rand (5)
//
  fn f (c: char):<cloref1> char =
    if c >= 'A' andalso c <= 'Z' then let
      val n = c - 'A'
      val n = int1_of_int (n)
      val () = assert (n >= 0); val () = assert (n < N)
      val v = enigma_encode (E, n)
    in
      char_of_int (int_of 'A' + v)
    end else c // end of [if]
  fn fs (msg1: string):<cloref1> string = let
    typedef charlst = List (char)
    val msg1 = string1_of_string (msg1)
    val cs1 = string_explode (msg1)
    val cs2 = list_map_cloref ($UN.castvwtp1 {charlst} (cs1), f)
    val () = list_vt_free (cs1)
    val msg2 = string_implode ($UN.castvwtp1 {charlst} (cs2))
    val () = list_vt_free (cs2)
  in
    string_of_strbuf (msg2)
  end // end of [fs]
//
  val msg1 = "HELLO, WORLD!"
  val () = println! ("msg1 = ", msg1)
//
  val () = enigma_init (E, 0 :: 0 :: 0 :: 0 :: 0 :: nil)  
  val msg2 = fs (msg1)
  val () = println! ("msg2 = ", msg2)
//
  val () = enigma_init (E, 0 :: 0 :: 0 :: 0 :: 0 :: nil)
  val msg3 = fs (msg2)
  val () = println! ("msg3 = ", msg3)
  val msg4 = fs (msg3)
  val () = println! ("msg4 = ", msg4)
//
(*
  val c0 = enigma_encode (E, 0)
  val () = printf ("%2.2d\n", @(c0))
  val c1 = enigma_encode (E, 1)
  val () = printf ("%2.2d\n", @(c1))
  val c2 = enigma_encode (E, 2)
  val () = printf ("%2.2d\n", @(c2))
*)
//
} // end of [main]

(* ****** ****** *)

(* end of [test.dats] *)

