(*
** Course: Concepts of Programming Languages (BU CAS CS 320)
** Semester: Summer I, 2009
** Instructor: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: June, 2009
//

(* ****** ****** *)

staload "absyn.sats"
staload "parser.sats"

(* ****** ****** *)

dynload "error.dats"
dynload "symbol.dats"
dynload "absyn.dats"
dynload "fixity.dats"
dynload "parser.dats"

dynload "PARCOMB/posloc.dats"
dynload "PARCOMB/tokenize.dats"
dynload "PARCOMB/parcomb.dats"

(* ****** ****** *)

implement main () = () where {
  val () = (print "stfpl_main: "; print_newline ())
  val prog = parse_from_stdin ()
  val () = print "prog =\n"
  val () = fprint_e0xp (stdout_ref, prog) 
  val () = print_newline ()
} // end of [main]

(* ****** ****** *)

(* end of [stfpl_main] *)