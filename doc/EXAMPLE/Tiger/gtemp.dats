(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload TL = "templab.sats"

(* ****** ****** *)

staload "gtemp.sats"

(* ****** ****** *)

assume gtempset_t = $TL.templst

(* ****** ****** *)

implement gtempset_nil () = '[]

(* ****** ****** *)

implement gtempset_ismem (gts, t0) =
  case+ gts of
  | list_cons (t, gts) => let
      val sgn = $TL.compare_temp_temp (t0, t)
    in
      if sgn < 0 then false
      else if sgn > 0 then gtempset_ismem (gts, t0)
      else true
    end // end of [list_cons]
  | list_nil () => false
// end of [gtempset_ismem]

(* ****** ****** *)

implement gtempset_add (gts, t0) = let
  var flag: int = 0 in gtempset_add_flag (gts, t0, flag)
end // end of [gtempset_add]

implement gtempset_add_flag
  (gts, t0, flag) = case+ gts of
  | list_cons (t, gts1) => let
      val sgn = $TL.compare_temp_temp (t0, t)
    in
      if sgn < 0 then let
        val () = flag := flag + 1 in list_cons (t0, gts)
      end else if sgn > 0 then
        list_cons (t, gtempset_add_flag (gts1, t0, flag))
      else gts
    end // end of [list_cons]
  | list_nil () => let
      val () = flag := flag + 1 in list_cons (t0, list_nil)
    end // end of [list_nil]
// end of [gtempset_insert]

(* ****** ****** *)

implement gtempset_union (gts1, gts2) = let
  var flag: int = 0 in gtempset_union_flag (gts1, gts2, flag)
end // end of [gtempset_union]

implement gtempset_union_flag
  (gts1, gts2, flag) = case+ (gts1, gts2) of
  | (list_cons (t1, gts1_tl), list_cons (t2, gts2_tl)) => let
      val sgn = $TL.compare_temp_temp (t2, t1)
    in
      if sgn < 0 then let
        val () =  flag := flag + 1 in
        list_cons (t2, gtempset_union_flag (gts1, gts2_tl, flag))
      end else if sgn > 0 then
        list_cons (t1, gtempset_union_flag (gts1_tl, gts2, flag))
      else begin
        list_cons (t1, gtempset_union_flag (gts1_tl, gts2_tl, flag))
      end // end of [if]
    end (* end of [list_cons, list_cons] *)
  | (_, list_nil ()) => gts1
  | (list_nil (), _) => (flag := flag + 1; gts2)
// end of [gtempset_union_flag]

(* ****** ****** *)

(* end of [gtemp.dats] *)
