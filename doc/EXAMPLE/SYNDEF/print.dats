(*
** some code for testing 'print!', 'println!' and 'fprint!'
*)

(* ****** ****** *)
//
val () = print! (tupz! 1 2 3 4 5 6 7 8 9 10)
val () = print_newline ()
val () = println! (tupz! 1 2 3 4 5 6 7 8 9 10)
//
val () = fprint! (stdout_ref, '0', 1, 02, 3U, 4L, 5UL, 6LL, 7ULL, 8.0, 9.0f, 0xA, "11")
val () = print_newline ()
val () = fprintln! (stdout_ref, '0', 1, 02, 3U, 4L, 5UL, 6LL, 7ULL, 8.0, 9.0f, 0xA, "11")
//
(* ****** ****** *)

implement main () = ()

(* ****** ****** *)

(* end of [print.dats] *)
