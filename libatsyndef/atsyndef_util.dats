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

implement
eq_intlst_intlst (ns1, ns2) =
  case+ ns1 of
  | list_cons (n1, ns1) => (case+ ns2 of
    | list_cons (n2, ns2) => (n1 = n2) andalso (ns1 = ns2)
    | list_nil () => false
    ) // end of [cons]
  | list_nil () => (
    case+ ns2 of list_cons _ => false | list_nil () => true
    ) // en dof [list_nil]
// end of [eq_list_list]

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
      val () = prerr_loc_syndef (d1e.d1exp_loc)
      val () = prerr ": the dynexp is expected be some annotated expression."
      val () = prerr_newline ()
    in
      $Err.abort ()
    end // end of [_]
// end of [un_d1exp_ann_type]

(* ****** ****** *)

implement
un_d1exp_qid (d1e) =
  case+ d1e.d1exp_node of
  | D1Eqid (q, id) =>  (q, id)
  | _ => let
      val () = prerr_loc_syndef (d1e.d1exp_loc)
      val () = prerr ": the dynexp is expected be some (qualified) identifier."
      val () = prerr_newline ()
    in
      $Err.abort ()
    end // end of [_]
// end of [un_d1exp_qid]

(* ****** ****** *)

implement
un_d1exp_idext (d1e) =
  case+ d1e.d1exp_node of
  | D1Eidextapp (id, _, _) => id
  | _ => let
      val () = prerr_loc_syndef (d1e.d1exp_loc)
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
    val () = prerr_loc_syndef (d1e.d1exp_loc)
    val () = prerr ": the dynexp is expected to be the idext `"
    val () = $Sym.prerr_symbol (sym0)
    val () = prerr "`"
    val () = prerr_newline ()
  in
    $Err.abort {void} ()
  end (* end of [if] *)
end // end of [un_d1exp_idext_sym]

(* ****** ****** *)

implement
un_d1exp_decseq
  (d1e) =
  case+ d1e.d1exp_node of
  | D1Edecseq (d1cs) => d1cs
  | _ => let
      val () = prerr_loc_syndef (d1e.d1exp_loc)
      val () = prerr ": the dynexp is expected to be a list of declarations."
      val () = prerr_newline ()
    in
      $Err.abort {d1eclst} ()
    end // end of [_]
// end of [un_d1exp_decseq]

(* ****** ****** *)

(* end of [atsyndef_util.dats] *)
