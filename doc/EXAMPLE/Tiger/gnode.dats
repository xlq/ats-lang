(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "gnode.sats"

(* ****** ****** *)

assume gnode_t = Nat

(* ****** ****** *)

implement gnode_make_int (n) = n

(* ****** ****** *)

implement fprint_gnode (out, gn) = fprint_int (out, gn)
implement print_gnode (gn) = fprint_gnode (stdout_ref, gn)
implement prerr_gnode (gn) = fprint_gnode (stderr_ref, gn)

(* ****** ****** *)

implement eq_gnode_gnode (gn1, gn2) = eq_int_int (gn1, gn2)

implement compare_gnode_gnode (gn1, gn2) = compare_int_int (gn1, gn2)

(* ****** ****** *)

assume gnodelst_t = List (gnode_t)

(* ****** ****** *)

implement gnodelst_nil () = '[]
implement gnodelst_sing (gn) = '[gn]

(* ****** ****** *)

implement fprint_gnodelst
  (out, gns) = loop (out, gns, 0) where {
  fun loop (out: FILEref, gns: gnodelst_t, i: int): void =
    case+ gns of
    | list_cons (gn, gns) => () where {
        val () = if i > 0 then fprint_string (out, ", ")
        val () = fprint_gnode (out, gn)
        val () = loop (out, gns, i+1)
      } // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
} // end of [fprint_gnodelst]

implement print_gnodelst (gns) = fprint_gnodelst (stdout_ref, gns)
implement prerr_gnodelst (gns) = fprint_gnodelst (stderr_ref, gns)

(* ****** ****** *)

implement gnodelst_ismem (gns, gn0) = case+ gns of
  | list_cons (gn, gns) =>
      if gn0 < gn then false
      else if gn0 > gn then gnodelst_ismem (gns, gn0)
      else true
    // end of [list_cons]
  | list_nil () => false
// end of [gnodelst_ismem]

(* ****** ****** *)

implement gnodelst_add (gns, gn0) = let
  var flag: int = 0 in gnodelst_add_flag (gns, gn0, flag)
end // end of [gnodelst_add]

implement gnodelst_add_flag
  (gns, gn0, flag) = case+ gns of
  | list_cons (gn, gns1) => begin
      if gn0 < gn then let
        val () = flag := flag + 1 in list_cons (gn0, gns)
      end else if gn0 > gn then
        list_cons (gn, gnodelst_add_flag (gns1, gn0, flag))
      else gns
    end // end of [list_cons]
  | list_nil () => let
      val () = flag := flag + 1 in list_cons (gn0, list_nil)
    end // end of [list_nil]
// end of [gnodelst_insert]

(* ****** ****** *)

implement gnodelst_union (gns1, gns2) = let
  var flag: int = 0 in gnodelst_union_flag (gns1, gns2, flag)
end // end of [gnodelst_union]

implement gnodelst_union_flag
  (gns1, gns2, flag) = case+ (gns1, gns2) of
  | (list_cons (gn1, gns1_tl), list_cons (gn2, gns2_tl)) => begin
      if gn2 < gn1 then let
        val () =  flag := flag + 1 in
        list_cons (gn2, gnodelst_union_flag (gns1, gns2_tl, flag))
      end else if gn2 > gn1 then
        list_cons (gn1, gnodelst_union_flag (gns1_tl, gns2, flag))
      else begin
        list_cons (gn1, gnodelst_union_flag (gns1_tl, gns2_tl, flag))
      end // end of [if]
    end (* end of [list_cons, list_cons] *)
  | (_, list_nil ()) => gns1
  | (list_nil (), _) => (flag := flag + 1; gns2)
// end of [gnodelst_union_flag]

(* ****** ****** *)

(* end of [gnode.sats] *)
