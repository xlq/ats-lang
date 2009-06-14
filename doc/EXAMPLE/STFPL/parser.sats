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
// A parser for STFPL (a simple typed functional programming language)
// The code was originally written by Hongwei Xi in May 2005
//

(* ****** ****** *)

staload POSLOC = "PARCOMB/posloc.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/option.dats"
staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

typedef loc_t = $POSLOC.location_t

(* ****** ****** *)

typedef id = String // may be replaced with a symbol table

datatype ty_node =
  | TYbase of id
  | TYfun of (tylst, ty)
  | TYpair of (ty, ty)
  | TYlist of tylst
  | TYvar of '{name= Nat, link= ref tyopt} // existential type variable
// end of [ty_node]

where ty = '{
  ty_loc= loc_t, ty_node= ty_node
} // end of [ty]
  and tyopt = Option ty and tylst = List ty
(* [tyopt] and [tylst] *)

fun fprint_ty (out: FILEref, _: ty): void

datatype e0xp_node =
  | E0XPvar of id
  | E0XPbool of Bool
  | E0XPint of Int
  | E0XPstr of String
  | E0XPop of (id, e0xplst)
  | E0XPif of (e0xp, e0xp, e0xp)
  | E0XPtup of e0xplst
  | E0XPproj of (e0xp, Int)
  | E0XPlist of e0xplst // for temporary use
  | E0XPfuns of f0deflst
  | E0XPchoose of (e0xp, Int)
  | E0XPapp of (e0xp, e0xp)
  | E0XPlet of (id, e0xp, e0xp)
  | E0XPann of (e0xp, ty)
// end of [e0xp_node]

where e0xp = '{
    e0xp_loc= loc_t, e0xp_nod= e0xp_node
  } // end of [e0xp]
  and e0xplst = List e0xp
  and a0rg = @(id, tyopt)
  and a0rglst = List a0rg
  and f0def = @{
    f0def_loc= loc_t
  , f0def_nam= id
  , f0def_arg= a0rglst
  , f0def_res= tyopt
  , f0def_def= e0xp
  } // end of [f0def]
  and f0deflst = List f0def

fun fprint_e0xp (out: FILEref, _: e0xp): void

(* ****** ****** *)

val parseFile: FILEref -> e0xp
val parseKeybd: () -> e0xp
val parseString: String -> e0xp

(* ****** ****** *)

(* end of [parser.sats] *)
