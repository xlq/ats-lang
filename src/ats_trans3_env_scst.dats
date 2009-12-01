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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: December 2007

(* ****** ****** *)

(* Mainly for handling environments during the third translation *)

(* ****** ****** *)

staload Err = "ats_error.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

local

assume s2cstlst_env_token = unit_v

viewtypedef s2cstlstlst_vt = List_vt s2cstlst
val the_s2cstlst: ref (s2cstlst) = ref_make_elt (S2CSTLSTnil ())
val the_s2cstlstlst: ref (s2cstlstlst_vt) = ref_make_elt (list_vt_nil ())

in

implement the_s2cstlst_env_add (s2c) = let
(*
  val () = begin
    print "the_s2cstlst_env_add: s2c = "; print s2c; print_newline ()
  end
*)
in
  !the_s2cstlst := S2CSTLSTcons (s2c, !the_s2cstlst)
end

implement the_s2cstlst_env_adds (s2cs) = let
(*
  val () = begin
    print "the_s2cstlst_env_adds: s2cs = "; print s2cs; print_newline ()
  end
*)
in
  !the_s2cstlst := s2cstlst_append (s2cs, !the_s2cstlst)
end

(* ****** ****** *)

implement the_s2cstlst_env_bind_and_add (loc0, s2c, s2e) = begin
  if not (s2cst_isasp_get s2c) then let
(*
    val () = begin
      print "the_s2cstlst_env_bind_and_add: s2c = "; print s2c; print_newline ();
      print "the_s2cstlst_env_bind_and_add: s2e = "; print s2e; print_newline ();
    end
*)
  in
    s2cst_def_set (s2c, Some s2e);
    s2cst_isasp_set (s2c, false);
    the_s2cstlst_env_add s2c;
  end else begin
    $Loc.prerr_location loc0;
    prerr ": error(3)";
    prerr ": the static constant ["; prerr s2c;
    prerr "] has already been assumed elsewhere.";
    prerr_newline ();
    $Err.abort {void} ()
  end
end // end of [the_s2cstlst_env_bind_ad_add]

(* ****** ****** *)

implement the_s2cstlst_env_pop (pf | (*none*)) = let
  prval unit_v () = pf; var err: int = 0
  val s2cs0 = !the_s2cstlst
  val () = let
    val (vbox pf | p) = ref_get_view_ptr (the_s2cstlstlst)
  in
    case+ !p of
    | ~list_vt_cons (s2cs, s2css) => let
        val () = $effmask_ref (!the_s2cstlst := (s2cs: s2cstlst))
      in
        !p := (s2css: s2cstlstlst_vt)
      end
    | ~list_vt_nil () => (err := 1; !p := list_vt_nil ())
  end // end of [val]
  val () = // for reporting an error
    if err > 0 then begin
      prerr "INTERNAL ERROR (ats_trans3_env_scst)";
      prerr ": the_s2cstlst_env_pop: [the_s2cstlstlst] is empty."; prerr_newline ();
      $Err.abort {void} ()
    end // end of [if]
  // end of [val]
in
  s2cs0
end // end of [the_s2cstlst_env_pop]

implement the_s2cstlst_env_pop_and_unbind (pf | (*none*)) = let
  fun aux (s2cs: s2cstlst): void = begin
    case+ s2cs of
    | S2CSTLSTcons (s2c, s2cs) => let
(*
        val () = begin
          print "the_s2cstlst_env_pop_and_unbind: aux: s2c = ";
          print s2c; print_newline ()
        end
*)
        val () = s2cst_def_set (s2c, None ())
      in
        aux s2cs
      end // end of [S2CSTLSTcons]
    | S2CSTLSTnil () => ()
  end // end of [aux]
in
  aux (the_s2cstlst_env_pop (pf | (*none*)))
end // end of [the_s2cstlst_env_pop_and_unbind]

(* ****** ****** *)

implement the_s2cstlst_env_push () = let
  val (vbox pf | p) = ref_get_view_ptr (the_s2cstlstlst)
  val s2cs = $effmask_ref (!the_s2cstlst)
  val () = $effmask_ref (!the_s2cstlst := S2CSTLSTnil ())
in
  !p := list_vt_cons (s2cs, !p); (unit_v () | ())
end // end of [the_s2cstlst_env_push]

end // end of [local]

(* ****** ****** *)

(* end of [ats_trans3_env_scst.sats] *)
