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

staload SYMBOL = "symbol.sats"
staload POSLOC = "PARCOMB/posloc.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/option.dats"
staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

typedef loc = $POSLOC.location_t

(* ****** ****** *)

typedef sym = $SYMBOL.symbol_t

datatype typ_node =
  | TYPbase of sym
  | TYPfun of (typlst, typ)
  | TYPpair of (typ, typ)
  | TYPlist of typlst
  | TYPxVar of @{name= int, link= ref typopt} // existential type variable
// end of [typ_node]

where typ = '{
  typ_loc= loc, typ_node= typ_node
} // end of [typ]
  and typopt = Option typ and typlst = List typ
(* [typopt] and [typlst] *)

(* ****** ****** *)

fun fprint_typ (out: FILEref, _: typ): void
fun fprint_typlst (out: FILEref, _: typlst): void

(* ****** ****** *)

fun typ_make_sym (_: loc, _: sym):<> typ 
fun typ_make_list (_: loc, _: typlst):<> typ
fun typ_make_fun (_: loc, arg: typlst, res: typ):<> typ

(* ****** ****** *)

datatype opr =
  | OPRplus | OPRminus
  | OPRtimes | OPRslash
  | OPRgt | OPRgte | OPRlt | OPRlte
  | OPReq | OPRneq
  | OPRuminus
// end of [opr]

fun fprint_opr (out: FILEref, opr: opr): void

(* ****** ****** *)

datatype e0xp_node =
  | E0XPann of (e0xp, typ)
  | E0XPapp of (e0xp, e0xp)
  | E0XPbool of bool
  | E0XPfix of (sym, a0rglst, typopt, e0xp)
  | E0XPif of (e0xp, e0xp, e0xpopt)
  | E0XPint of int
  | E0XPlam of (a0rglst, typopt, e0xp)
  | E0XPlet of (d0eclst, e0xp)
  | E0XPlist of e0xplst // for temporary use
  | E0XPopr of (opr, e0xplst)
  | E0XPproj of (e0xp, int)
  | E0XPstr of string
  | E0XPtup of e0xplst
  | E0XPvar of sym
// end of [e0xp_node]

and d0ec_node =
  | D0ECval of (bool(*isrec*), v0aldeclst)
// end of [d0ec_node]

where e0xp = '{
    e0xp_loc= loc, e0xp_node= e0xp_node
  } // end of [e0xp]

and e0xplst = List e0xp
and e0xpopt = Option e0xp

and a0rg = @{
  a0rg_loc= loc, a0rg_nam= sym, a0rg_typ= typopt
} // end of [a0rg] 
and a0rglst = List a0rg

and d0ec = @{
  d0ec_loc= loc, d0ec_node= d0ec_node
}

and d0eclst = List (d0ec)

and v0aldec = @{
  v0aldec_loc= loc
, v0aldec_nam= sym
, v0aldec_ann= typopt
, v0aldec_def= e0xp
}
and v0aldeclst = List (v0aldec)

// end of [where]

(* ****** ****** *)

fun fprint_e0xp (out: FILEref, _: e0xp): void
fun fprint_e0xplst (out: FILEref, _: e0xplst): void

(* ****** ****** *)

fun e0xp_make_ann (_: loc, e: e0xp, t: typ):<> e0xp
fun e0xp_make_app (_: loc, _fun: e0xp, _arg: e0xp):<> e0xp
fun e0xp_make_bool (_: loc, _: bool):<> e0xp
fun e0xp_make_fix (_: loc, _: sym, _: a0rglst, _: typopt, _: e0xp):<> e0xp
fun e0xp_make_if (_: loc, _: e0xp, _: e0xp, _: e0xpopt):<> e0xp
fun e0xp_make_int (_: loc, _: int):<> e0xp
fun e0xp_make_lam (_: loc, _: a0rglst, _: typopt, _: e0xp):<> e0xp
fun e0xp_make_let (_: loc, ds: d0eclst, e: e0xp):<> e0xp
fun e0xp_make_list (_: loc, _: e0xplst):<> e0xp
fun e0xp_make_opr (_: loc, _: opr, _: e0xplst):<> e0xp
fun e0xp_make_proj (_: loc, e: e0xp, i: int):<> e0xp
fun e0xp_make_str (_: loc, _: string):<> e0xp
fun e0xp_make_tup (_: loc, _: e0xplst):<> e0xp
fun e0xp_make_var (_: loc, _: sym):<> e0xp

(* ****** ****** *)

fun d0ec_make_val (_: loc, isrec: bool, vds: v0aldeclst):<> d0ec 

(* ****** ****** *)

(* end of [absyn.sats] *)
