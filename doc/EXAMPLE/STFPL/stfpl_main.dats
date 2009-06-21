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
staload "trans1.sats"

(* ****** ****** *)

dynload "error.dats"
dynload "symbol.dats"
dynload "absyn.dats"
dynload "fixity.dats"

dynload "PARCOMB/posloc.dats"
dynload "PARCOMB/tokenize.dats"
dynload "PARCOMB/parcomb.dats"

dynload "parser.dats"
dynload "trans1.dats"

(* ****** ****** *)

implement main () = () where {
  val () = (print "stfpl_main: "; print_newline ())
  val prog = parse_from_stdin ()
  val () = print "prog =\n"
  val () = fprint_e0xp (stdout_ref, prog) 
  val () = print_newline ()
  val e1xp = trans1_exp (prog)
  val t1yp = e1xp.e1xp_typ
  val () = (print "t1yp = "; print_t1yp t1yp; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [stfpl_main] *)