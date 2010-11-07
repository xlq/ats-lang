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

staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t
staload Lst = "ats_list.sats"
staload Sym = "ats_symbol.sats"
overload = with $Sym.eq_symbol_symbol

(* ****** ****** *)

staload "ats_dynexp1.sats"
staload "ats_dynexp1_syndef.sats"

(* ****** ****** *)

(*
dynload "libatsyndef/atsyndef_main.dats"
*)

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

fn prerr_loc_error1
  (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(1)")
// end of [prerr_loc_error1]

(* ****** ****** *)

implement
fprint_intlst
  (out, ns) = let
  fun loop (
    out: FILEref, ns: intlst, i: int
  ) : void =
    case+ ns of
    | list_cons (n, ns) => let
        val () = if i > 0 then
          fprint_string (out, ", ")
        val () = fprint_int (out, n)
      in
        loop (out, ns, i+1)
      end // end of [cons]
    | list_nil () => ()
  // end of [loop]
in
  loop (out, ns, 0)
end // end of [fprint_intlst]

(* ****** ****** *)

implement
match_intlst_intlst (ns1, ns2) =
  case+ ns1 of
  | list_cons (n1, ns1) => (case+ ns2 of
    | list_cons (n2, ns2) => (
        if n2 >= 0 then
          (if (n1 = n2) then match_intlst_intlst (ns1, ns2) else false)
        else match_intlst_intlst (ns1, ns2)
      ) // end of [list_cons]
    | list_nil () => false
    ) // end of [cons]
  | list_nil () => (
    case+ ns2 of list_cons _ => false | list_nil () => true
    ) // end of [list_nil]
// end of [match_intlst_intlst]

(* ****** ****** *)

implement
tmpqi0de_make_qid
  (loc, q, id) = '{
  tmpqi0de_loc= loc, tmpqi0de_qua= q, tmpqi0de_sym= id
} // end of [tmpqi0de_make_qid]

(* ****** ****** *)

implement
un_d1exp_ann_type
  (d1e) = case+ d1e.d1exp_node of
  | D1Eann_type (d1e, s1e) => (d1e, s1e)
  | _ => let
      val () = prerr_loc_error1 (d1e.d1exp_loc)
      val () = prerr ": the dynexp is expected be some annotated expression."
      val () = prerr_newline ()
    in
      $Err.abort ()
    end // end of [_]
// end of [un_d1exp_ann_type]

(* ****** ****** *)

implement
un_d1exp_idext (d1e) =
  case+ d1e.d1exp_node of
  | D1Eidextapp (id, _, _) => id
  | _ => let
      val () = prerr_loc_error1 (d1e.d1exp_loc)
      val () = prerr ": the dynexp is expected to be some external identifer."
      val () = prerr_newline ()
    in
      $Err.abort {sym_t} ()
    end // end of [_]
// end of [un_d1exp_idext]

implement
un_d1exp_idext_sym
  (d1e, sym0) = let
  val sym = un_d1exp_idext (d1e)
in
  if $Sym.eq_symbol_symbol
    (sym0, sym) then () else let
    val () = prerr_loc_error1 (d1e.d1exp_loc)
    val () = (
      prerr ": the external id ["; $Sym.prerr_symbol (sym0); prerr "] is expected."
    ) // end of [val]
    val () = prerr_newline ()
  in
    $Err.abort {void} ()
  end (* end of [if] *)
end // end of [un_d1exp_idext_sym]

(* ****** ****** *)

implement
un_d1exp_qid (d1e) =
  case+ d1e.d1exp_node of
  | D1Eqid (q, id) =>  (q, id)
  | _ => let
      val () = prerr_loc_error1 (d1e.d1exp_loc)
      val () = prerr ": the dynexp is expected be some (qualified) identifier."
      val () = prerr_newline ()
    in
      $Err.abort ()
    end // end of [_]
// end of [un_d1exp_qid]

implement
un_d1exp_qid_sym
  (d1e, sym0) = let
  val (q, sym) = un_d1exp_qid (d1e)
in
  if $Sym.eq_symbol_symbol
    (sym0, sym) then () else let
    val () = prerr_loc_error1 (d1e.d1exp_loc)
    val () = (
      prerr ": the symbol ["; $Sym.prerr_symbol (sym0); prerr "] is expected."
    ) // end of [val]
    val () = prerr_newline ()
  in
    $Err.abort {void} ()
  end (* end of [if] *)
end // end of [un_d1exp_qid_sym]

(* ****** ****** *)

implement
un_d1exp_decseq
  (d1e) =
  case+ d1e.d1exp_node of
  | D1Edecseq (d1cs) => d1cs
  | _ => let
      val () = prerr_loc_error1 (d1e.d1exp_loc)
      val () = prerr ": the dynexp is expected to be a list of declarations."
      val () = prerr_newline ()
    in
      $Err.abort {d1eclst} ()
    end // end of [_]
// end of [un_d1exp_decseq]

(* ****** ****** *)
//
// HX-2010-11-02:
// this function is implemented in
// $ATSHOME/utils/syndef/atsyndef_main.dats
//
typedef
atsyndef_search_all_type =
  (sym_t, intlst) -<fun1> Option_vt (fsyndef)
extern
fun atsyndef_search_all: atsyndef_search_all_type
// end of [extern]

(* ****** ****** *)

val _n1_p1 = (~1 :: 1 :: nil): intlst // while ($test) 
val _n1_p1_n1 =
  (~1 :: 1 :: ~1 :: nil): intlst // do ($body) while ($test)
// end of [val]

(* ****** ****** *)

macdef matii = match_intlst_intlst

(* ****** ****** *)

extern
fun search_DO
  (ns: intlst): fsyndefopt
extern
fun d1exp_do_n1_p1_n1
  (loc: loc_t, d1es: d1explst): d1exp
// end of [d1exp_do_n1_p1_n1]

implement
search_DO (ns) = let
(*
  val () = print "search_DO: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when ns \matii _n1_p1_n1 => Some_vt (d1exp_do_n1_p1_n1)
  | _ => None_vt ()
end // end of [search_DO]

(* ****** ****** *)

extern
fun search_WHILE
  (ns: intlst): fsyndefopt
extern
fun d1exp_while_n1_p1
  (loc: loc_t, d1es: d1explst): d1exp
// end of [d1exp_while_n1_p1]

implement
search_WHILE (ns) = let
(*
  val () = print "search_WHILE: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when ns \matii _n1_p1 => Some_vt (d1exp_while_n1_p1)
  | _ => None_vt ()
end // end of [search_WHILE]

implement
atsyndef_search_all_default
  (id, ns) = let
(*
  val () = print "atsyndef_search_all_default: id = "
  val () = $Sym.print_symbol (id)
  val () = print_newline ()
  val () = print "atsyndef_search_all_default: ns = "
  val () = fprint_intlst (stdout_ref, ns)
  val () = print_newline ()
*)
in
  case+ 0 of
  | _ when id = $Sym.symbol_DO => search_DO (ns)
  | _ when id = $Sym.symbol_WHILE => search_WHILE (ns)
  | _ => None_vt ()
end // end of [atsyndef_search_all_default]

(* ****** ****** *)

(*
// HX: compile with the -DATS_SYNDEFATS flag
#define _SYNDEFATS 1
*)
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
  (id, ns) = let
  val ans = atsyndef_search_all_default (id, ns)
in
  case+ ans of
  | ~None_vt _ => (case+ 0 of
    | _ when fsrch_ptr > null => let
        val fsrch = __cast (fsrch_ptr) where {
          extern castfn __cast (x: ptr):<> atsyndef_search_all_type
        } // end of [_ when ...]
      in
        fsrch (id, ns)
      end // end of [_ when ...]
    | _ => None_vt ()
    ) // end of [None_vt]
  | Some_vt _ => (fold@ ans; ans)
end // end of [atsyndef_search_all]

end  // end of [local]

#else // else of [_SYNDEFATS]

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

implement
d1exp_do_n1_p1_n1
  (loc0, d1es) = let
//
  val- cons (d1e3, d1es) = d1es
//
  val- cons (d1e2, d1es) = d1es
  val () = un_d1exp_idext_sym (d1e2, $Sym.symbol_WHILE)
//
  val- cons (d1e1, d1es) = d1es
//
  val _then = d1exp_loopexn (loc0, 1) // continue
  val _else = Some (d1exp_loopexn (loc0, 0)) // break
//
  val loc3 = d1e3.d1exp_loc
  val _ifexp = d1exp_if (loc3, i1nvresstate_nil, d1e3, _then, _else)
//
  val _inv = loopi1nv_nil (loc0)
  val _true = d1exp_bool (loc0, true)
//
  val _body = d1exp_seq (loc0, d1e1 :: _ifexp :: nil)
//
in
  d1exp_while (loc0, _inv, _true, _body)
end // end of [do_n1_p1_n1]

(* ****** ****** *)

implement
d1exp_while_n1_p1
  (loc0, d1es) = let
//
  val- cons (d1e2, d1es) = d1es
  val _body = d1e2
//
  val- cons (d1e1, d1es) = d1es
  val _test = d1e1
//
  val _inv = loopi1nv_nil (loc0)
//
in
  d1exp_while (loc0, _inv, _test, _body)
end // end of [d1exp_while_n1_p1]

(* ****** ****** *)

(* end of [ats_dynexp1_syndef.dats] *)
