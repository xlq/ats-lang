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

staload "ats_syndef.sats"

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
extern fun atsyndef_search_all
  (id: sym_t, ns: intlst): Option_vt (fsyndef_t) = "atsyndef_search_all"
// end of [atsyndef_search_all]

implement
atsyndef_search_all (id, ns) = None_vt ()

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

(* end of [ats_syndef.dats] *)
