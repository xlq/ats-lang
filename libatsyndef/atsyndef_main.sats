(*
**
** Some utility functions for supporting syndef
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** Time: November, 2010
**
*)

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // there is no need for staloading at run-time

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"

(* ****** ****** *)

typedef fsyndef_t =
  (loc_t, d1explst) -<fun1> d1exp
// end of [typedef]

(* ****** ****** *)

fun do_search (ns: intlst): Option_vt (fsyndef_t)

(* ****** ****** *)

fun forlist_search (ns: intlst): Option_vt (fsyndef_t)

(* ****** ****** *)

fun print_search (ns: intlst): Option_vt (fsyndef_t)
fun println_search (ns: intlst): Option_vt (fsyndef_t)

(* ****** ****** *)

(* end of [atsyndef_main.sats] *)
