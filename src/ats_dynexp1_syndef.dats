(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August 2007
//
(* ****** ****** *)

staload
Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_dynexp1.sats"

(* ****** ****** *)

(*
dynload "libatsyndef/atsyndef_main.dats"
*)

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

typedef intlst = List (int)
typedef fsyndef_t = (loc_t, d1explst) -<fun1> d1exp

//
// HX-2010-11-02:
// this function is implemented in
// $ATSHOME/utils/syndef/atsyndef_main.dats
//
typedef
atsyndef_search_all_type =
  (sym_t, intlst) -<fun1> Option_vt (fsyndef_t)
extern
fun atsyndef_search_all: atsyndef_search_all_type
// end of [extern]

(* ****** ****** *)

fun atsyndef_search_all_default
  (id: sym_t, ns: intlst) = None_vt ()
// end of [atsyndef_search_all_default]

(* ****** ****** *)

#define _SYNDEFATS
#if defined(_SYNDEFATS) #then
//
local
//
staload "libc/SATS/dlfcn.sats"
//
val finit_name = "atsyndef_initialize"
var finit_ptr: ptr = null
//
val fsrch_name = "atsyndef_search_all"
var fsrch_ptr: ptr = null
//
val (pfopt_lib | p_lib) =
  dlopen ("libatsyndef.so", RTLD_LAZY)
// end of [val]
val () = if
p_lib > null then let
  val () = (prerr "\
ATS/Anairiats: [libatsyndef.so] is available to support syndef-loaded external ids.\n\
"
  ) // end of [val]
  prval Some_v (pf_lib) = pfopt_lib
  val () = dlerror_clr ()
  val () = finit_ptr := dlsym (pf_lib | p_lib, finit_name)
(*
  val (fpf_msg | msg) = dlerror () // clearing any existing error
  val () = (
    print "atsyndef_search_all: finit: "; print msg; print_newline ()
  ) // end of [val]
  prval () = fpf_msg (msg)
*)
  val () = dlerror_clr ()
  val () = fsrch_ptr := dlsym (pf_lib | p_lib, fsrch_name)
(*
  val (fpf_msg | msg) = dlerror () // see if there is any error
  val () = (
    print "atsyndef_search_all: fsrch = "; print msg; print_newline ()
  ) // end of [val]
  prval () = fpf_msg (msg)
*)
  val () = dlclose_exn (pf_lib | p_lib)
in
  // nothing
end else let
  val () = (prerr "\
ATS/Anairiats: [libatsyndef.so] is not available to support syndef-loaded external ids.\n\
"
  ) // end of [val]
  prval None_v () = pfopt_lib
in
  // nothing
end // end of [if]
//
val finit_ptr = finit_ptr
val fsrch_ptr = fsrch_ptr
//
val () = if
  finit_ptr > null then let
  val finit = __cast (finit_ptr) where {
    extern castfn __cast (x: ptr):<> ((*none*)) -<fun1> void
  } // end of [val]
in
  finit ()
end // end of [val]

in // in of [local]

implement
atsyndef_search_all
  (id, ns) = case+ 0 of
  | _ when fsrch_ptr > null => let
      val fsrch = __cast (fsrch_ptr) where {
        extern castfn __cast (x: ptr):<> atsyndef_search_all_type
      } // end of [_ when ...]
    in
      fsrch (id, ns)
    end // end of [_ when ...]
  | _ => atsyndef_search_all_default (id, ns)
// end of [atsyndef_search_all]

end  // end of [local]

#else

implement
atsyndef_search_all
  (id, ns) = atsyndef_search_all_default (id, ns)
// end of [atsyndef_search_all]

#endif // end of [_SYNDEFATS]

(* ****** ****** *)

implement
d1exp_app_dyn_syndef (
  loc0, d1e_fun, loc_arg, npf, d1es_arg
) =
  case+ d1e_fun.d1exp_node of
  | D1Eidextapp
      (id, ns, arglst) => let
      val n = $Lst.list_length (d1es_arg)
      val ns = cons (n, ns)
      val arg = d1exp_list (loc_arg, d1es_arg)
      val arglst = cons (arg, arglst)
      val opt = atsyndef_search_all (id, ns)
    in
      case+ opt of
      | ~Some_vt (fsyndef) => fsyndef (loc0, arglst)
      | ~None_vt () => d1exp_idextapp (loc0, id, ns, arglst)
    end // end of [D1Eidexpapp]
  | _ => d1exp_app_dyn
      (loc0, d1e_fun, loc_arg, npf, d1es_arg)
    // end of [_]
// end of [d1exp_app_dyn_syndef]

(* ****** ****** *)

(* end of [ats_dynexp1_syndef.dats] *)
