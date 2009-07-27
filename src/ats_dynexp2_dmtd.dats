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
// Time: July 2009

(* ****** ****** *)

staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t

staload Sym = "ats_symbol.sats"
typedef sym_t = $Sym.symbol_t

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

typedef d2mtd_struct = struct {
  d2mtd_loc= loc_t
, d2mtd_sym= sym_t
, d2mtd_knd= mtdkind
, d2mtd_decarg= s2qualst
, d2mtd_sublst= List @(s2qualst, tmps2explstlst)
, d2mtd_subtyp= s2exp
, d2mtd_typopt= s2expopt
, d2mtd_stamp= stamp_t // uniqueness stamp
} // end of [d2mtd_struct]

(* ****** ****** *)

local

assume d2mtd_t =
  [l:addr] (vbox (d2mtd_struct @ l) | ptr l)
// end of [assume]

in // in of [local]

implement d2mtd_make
  (loc, name, knd, decarg, sublst, subtyp) = let

val stamp = $Stamp.d2mac_stamp_make ()
val (pf_gc, pf | p) =
  ptr_alloc_tsz {d2mtd_struct} (sizeof<d2mtd_struct>)
// end of [val]
prval () = free_gc_elim {d2mtd_struct} (pf_gc)

val () = begin
p->d2mtd_loc := loc;
p->d2mtd_sym := name;
p->d2mtd_knd := knd;
p->d2mtd_decarg := decarg;
p->d2mtd_sublst := sublst;
p->d2mtd_subtyp := subtyp;
p->d2mtd_typopt := None ();
p->d2mtd_stamp := stamp;
end // end of [val]

val (pfbox | ()) = vbox_make_view_ptr (pf | p)

in // in of [let]

(pfbox | p)

end // end of [d2mtd_make]

implement d2mtd_loc_get (d2m) =
  let val (vbox pf | p) = d2m in p->d2mtd_loc end
// end of [d2mtd_loc_get]

implement d2mtd_sym_get (d2m) =
  let val (vbox pf | p) = d2m in p->d2mtd_sym end
// end of [d2mtd_sym_get]

implement d2mtd_knd_get (d2m) =
  let val (vbox pf | p) = d2m in p->d2mtd_knd end
// end of [d2mtd_knd_get]

implement d2mtd_decarg_get (d2m) =
  let val (vbox pf | p) = d2m in p->d2mtd_decarg end
// end of [d2mtd_decarg_get]

implement d2mtd_sublst_get (d2m) =
  let val (vbox pf | p) = d2m in p->d2mtd_sublst end
// end of [d2mtd_sublst_get]

implement d2mtd_subtyp_get (d2m) =
  let val (vbox pf | p) = d2m in p->d2mtd_subtyp end
// end of [d2mtd_subtyp_get]

implement d2mtd_stamp_get (d2m) =
  let val (vbox pf | p) = d2m in p->d2mtd_stamp end
// end of [d2mtd_stamp_get]

(* ****** ****** *)

implement d2mtd_typ_get (d2m) = let
  typedef sub_t = @(s2qualst, tmps2explstlst)
  fun aux // caching if needed
    (subs: List sub_t, res: s2exp): s2exp =
    case+ subs of
    | list_cons (sub, subs) => let
        val res = aux (subs, res)
        val stasub = let
          fun stasubext (
              stasub: stasub_t
            , s2qss: s2qualst
            , ts2ess: tmps2explstlst
            ) : stasub_t =
            case+ (s2qss, ts2ess) of
            | (list_cons (s2qs, s2qss),
               TMPS2EXPLSTLSTcons (_loc, s2es, ts2ess)) => let
                val stasub = stasub_addlst (stasub, s2qs.0, s2es)
              in
                stasubext (stasub, s2qss, ts2ess)
              end // end of [list_cons, TMPS2EXPLSTcons]
            | (_, _) => stasub
          // end of [stasubext]
        in
          stasubext (stasub_nil, sub.0, sub.1)
        end (* end of [list_cons] *)
      in
        s2exp_subst (stasub, res)
      end // end of [list_cons]
    | list_nil () => res
  // end of [aux]
  val os2e = let
    val (vbox pf | p) = d2m in p->d2mtd_typopt
  end // end of [val]
in
  case+ os2e of
  | Some s2e => s2e
  | None () => let
      val sublst = let
        val (vbox pf | p) = d2m in p->d2mtd_sublst
      end // end of [val]
      val subtyp = let
        val (vbox pf | p) = d2m in p->d2mtd_subtyp
      end // end of [val]
      val typ = aux (sublst, subtyp)
      val () = let
        val (vbox pf | p) = d2m in p->d2mtd_typopt := Some typ
      end // end of [val]
    in
      typ
    end (* end of [None] *)
end (* end of [d2mtd_typ_get] *)

(* ****** ****** *)

end // end of [local]

(* ****** ****** *)

implement fprint_d2mtd (pf_out | out, d2m) = begin
  $Sym.fprint_symbol (pf_out | out, d2mtd_sym_get d2m)
end // end of [fprint_d2mtd]

implement print_d2mtd (d2m) = print_mac (fprint_d2mtd, d2m)
implement prerr_d2mtd (d2m) = prerr_mac (fprint_d2mtd, d2m)

(* ****** ****** *)

(* end of [ats_dynexp2_dmtd.dats] *)
