(*
**
** Some utility functions for supporting syndef
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: November, 2010
**
*)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // there is no need for dynloading at run-time
#define ATS_DYNLOADFUN_NAME "atsyndef_initialize"

(* ****** ****** *)

staload Sym = "ats_symbol.sats"
typedef sym_t = $Sym.symbol_t
overload = with $Sym.eq_symbol_symbol

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"
staload "ats_dynexp1_syndef.sats"

(* ****** ****** *)

staload "atsyndef_main.sats"

(* ****** ****** *)

val symbol_DO = $Sym.symbol_DO
val symbol_FOR = $Sym.symbol_FOR

(* ****** ****** *)
(*
//
// HX-2010-11-02:
// this is the C interface for [atsyndef_search_all]:
//
extern
ats_ptr_type
atsyndef_search_all (ats_ptr_type id, ats_ptr_type ns) ;
*)
extern
fun atsyndef_search_all
  (id: sym_t, ns: List (int)): Option_vt (fsyndef_t)
  = "atsyndef_search_all"
// end of [atsyndef_search_all]

implement
atsyndef_search_all
  (id, ns) = case+ 0 of
  | _ when id = symbol_FOR => search_FOR (ns)
  | _ => None_vt ()
// end of [search_all]

(* ****** ****** *)

dynload "atsyndef_FOR.dats"

(* ****** ****** *)

(* end of [atsyndef_main.dats] *)
