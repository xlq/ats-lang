(*
** some testing code for functions declared in
** libc/SATS/stdlib.sats
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: May, 2009
//

(* ****** ****** *)

staload "libc/SATS/stdlib.sats"

(* ****** ****** *)

// listing all of the files in a given directory
implement main (argc, argv) = let
  val () = atexit_exn (lam () => printf ("Bye, bye!\n", @()))
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [libc_stdlib.dats] *)
