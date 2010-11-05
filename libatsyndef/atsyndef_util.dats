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

#define ATS_DYNLOADFLAG 0 // there is no need for dynloading at run-time

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"

(* ****** ****** *)

staload "atsyndef_util.sats"

(* ****** ****** *)

fn prerr_loc_syndef
  (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(syndef)")
// end of [prerr_loc_syndef]

(* ****** ****** *)

(* end of [atsyndef_util.dats] *)
