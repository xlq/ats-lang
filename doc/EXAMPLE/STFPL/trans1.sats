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

//
// A typechecker for STFPL (a simple typed functional programming language)
// The code was originally written by Hongwei Xi in May 2005
//

(* ****** ****** *)

staload SYMBOL = "symbol.sats"
typedef sym = $SYMBOL.symbol_t

(* ****** ****** *)

staload POSLOC = "PARCOMB/posloc.sats"
typedef loc = $POSLOC.location_t

(* ****** ****** *)

staload ABSYN = "absyn.sats"
typedef typ = $ABSYN.typ
typedef typopt = $ABSYN.typopt
typedef opr = $ABSYN.opr

(* ****** ****** *)

datatype e1xp_node =
  | E1XPann of (e1xp, typ)
  | E1XPapp of (e1xp, e1xp)
  | E1XPbool of bool
  | E1XPfix of (sym, v1arlst, typopt, e1xp)
  | E1XPif of (e1xp, e1xp, e1xpopt)
  | E1XPint of int
  | E1XPlam of (v1arlst, typopt, e1xp)
(*
  | E1XPlet of (d1eclst, e1xp)
*)
  | E1XPopr of (opr, e1xplst)
  | E1XPproj of (e1xp, int)
  | E1XPstr of string
  | E1XPtup of e1xplst
  | E1XPvar of v1ar

where e1xp = '{
  e1xp_loc= loc, e1xp_node= e1xp_node
} // end of [e1xp]

and e1xplst = List (e1xp)
and e1xpopt = Option (e1xp)

and v1ar = '{
  v1ar_loc= loc, v1ar_nam= sym, v1ar_typ= typ
} // end of [v1ar]
and v1arlst = List (v1ar)

(* ****** ****** *)

fun trans1 (_: $ABSYN.e0xp): e1xp

(* ****** ****** *)

(* end of [trans1.sats] *)
