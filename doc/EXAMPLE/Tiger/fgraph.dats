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
staload "gtemp.sats"

(* ****** ****** *)

staload TL = "templab.sats"

(* ****** ****** *)

staload "fgraph.sats"

(* ****** ****** *)

local

typedef fgnodeinfo = '{
  node= gnode_t
, pred= gnodelst_t(*pred*)
, succ= gnodelst_t(*succ*)
, uselst= $TL.templst, deflst= $TL.templst
, inset= gtempset_t, outset= gtempset_t
}

assume fgnodeinfo_t = fgnodeinfo

in // in of [local]

extern typedef "fgnodeinfo_t" = fgnodeinfo

extern fun fgnodeinfo_pred_set
  (rep: fgnodeinfo_t, gns: gnodelst_t): void
  = "fgnodeinfo_pred_set"

extern fun fgnodeinfo_succ_set
  (rep: fgnodeinfo_t, gns: gnodelst_t): void
  = "fgnodeinfo_succ_set"

implement fgnodeinfo_make
  (gn, uselst, deflst) = '{
  node= gn
, pred= gnodelst_nil (), succ= gnodelst_nil ()
, uselst= uselst, deflst= deflst
, inset= gtempset_nil (), outset= gtempset_nil ()
} // end of [fgnodeinfo_make]

implement fgnodeinfo_pred_get (info) = info.pred
implement fgnodeinfo_succ_get (info) = info.succ

implement fprint_fgnodeinfo (out, info) = () where {
  val () = fprint_string (out, "node= ")
  val () = fprint_gnode (out, info.node)
  val () = fprint_newline (out)
  val () = fprint_string (out, "pred= ")
  val () = fprint_gnodelst (out, info.pred)
  val () = fprint_newline (out)
  val () = fprint_string (out, "succ= ")
  val () = fprint_gnodelst (out, info.succ)
  val () = fprint_newline (out)
  val () = fprint_string (out, "uselst= ")
  val () = $TL.fprint_templst (out, info.uselst)
  val () = fprint_newline (out)
  val () = fprint_string (out, "deflst= ")
  val () = $TL.fprint_templst (out, info.deflst)
  val () = fprint_newline (out)
  val () = fprint_string (out, "inset= ")
  val () = fprint_newline (out)
  val () = fprint_string (out, "outset= ")
  val () = fprint_newline (out)
} // end of [fprint_fgnodeinfo]

end // end of [local]

implement print_fgnodeinfo (info) = fprint_fgnodeinfo (stdout_ref, info)
implement prerr_fgnodeinfo (info) = fprint_fgnodeinfo (stderr_ref, info)

(* ****** ****** *)

staload "LIB/funarray.dats"

(* ****** ****** *)

assume fgraph_t (n:int) = funarray_t (fgnodeinfo_t, n)

(* ****** ****** *)

implement fgraph_empty () = funarray_empty ()

implement fgraph_extend (fg, n, info) = funarray_hiadd (fg, n, info)

(* ****** ****** *)

implement fprint_fgraph (out, fg) = let
  val n = funarray_length (fg)
  fun loop {n,i:nat | i <= n} .<n-i>.
    (out: FILEref, fg: fgraph_t n, n: int n, i: int i): void =
    if i < n then let
      val info = funarray_get_elt_at (fg, i)
      val () = fprint_fgnodeinfo (out, info)
      val () = fprint_newline (out)
    in
      loop (out, fg, n, i + 1)
    end // end of [if]
  // end of [loop
in
  loop (out, fg, n, 0)
end (* end of [fprint_fgraph] *)


(* ****** ****** *)

implement fgraph_nodeinfo_get (fg, n) = let
  val n = int_of_gnode (n) in funarray_get_elt_at_exn (fg, n)
end // end of [fgraph_nodeinfo_get]

implement
  fgraph_node_predlst_get (fg, n) = let
  val info = fgraph_nodeinfo_get (fg, n) in
  fgnodeinfo_pred_get (info)
end // end of [fgraph_node_predlst_get]

implement
  fgraph_node_succlst_get (fg, n) = let
  val info = fgraph_nodeinfo_get (fg, n) in
  fgnodeinfo_succ_get (info)
end // end of [fgraph_node_succlst_get]

(* ****** ****** *)

implement fgraph_edge_insert
  (fg, gn_fr, gn_to) = () where {
// modifying the representation for [n_fr]
  val () = () where {
    val info = fgraph_nodeinfo_get (fg, gn_fr)
    val gns_succ = fgnodeinfo_succ_get (info)
    val gns_succ = gnodelst_add (gns_succ, gn_to)
    val () = fgnodeinfo_succ_set (info, gns_succ)
  } // end of [val]
// modifying the representation for [n_to]
  val () = () where {
    val info = fgraph_nodeinfo_get (fg, gn_to)
    val gns_pred = fgnodeinfo_pred_get (info)
    val gns_pred = gnodelst_add (gns_pred, gn_fr)
    val () = fgnodeinfo_pred_set (info, gns_pred)
  } // end of [val]
} // end of [fgraph_edge_insert]

(* ****** ****** *)

%{$

ats_void_type
fgnodeinfo_pred_set
  (ats_ptr_type info, ats_ptr_type predlst) {
  ((fgnodeinfo_t)info)->atslab_pred = predlst ; return ;
}

ats_void_type
fgnodeinfo_succ_set
  (ats_ptr_type info, ats_ptr_type succlst) {
  ((fgnodeinfo_t)info)->atslab_succ = succlst ; return ;
}

%}

(* ****** ****** *)

(* end of [fgraph.dats] *)
