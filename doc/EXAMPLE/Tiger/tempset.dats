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

staload "tempset.sats"

(* ****** ****** *)

assume tempset_t = $TL.templst

(* ****** ****** *)

implement tempset_nil () = '[]

implement tempset_make_templst (ts) = let
  fun loop (ts: $TL.templst, res: tempset_t): tempset_t =
    case+ ts of
    | list_cons (t, ts) => loop (ts, tempset_add (res, t))
    | list_nil () => res
in
  loop (ts, list_nil ())
end // end of [tempset_make_templst]

(* ****** ****** *)

implement fprint_tempset (out, ts) = $TL.fprint_templst (out, ts)

(* ****** ****** *)

implement tempset_ismem (ts, t0) =
  case+ ts of
  | list_cons (t, ts) => let
      val sgn = $TL.compare_temp_temp (t0, t)
    in
      if sgn < 0 then false
      else if sgn > 0 then tempset_ismem (ts, t0)
      else true
    end // end of [list_cons]
  | list_nil () => false
// end of [tempset_ismem]

(* ****** ****** *)

implement tempset_add (ts, t0) = let
  var flag: int = 0 in tempset_add_flag (ts, t0, flag)
end // end of [tempset_add]

implement tempset_add_flag
  (ts, t0, flag) = case+ ts of
  | list_cons (t, ts1) => let
      val sgn = $TL.compare_temp_temp (t0, t)
    in
      if sgn < 0 then let
        val () = flag := flag + 1 in list_cons (t0, ts)
      end else if sgn > 0 then
        list_cons (t, tempset_add_flag (ts1, t0, flag))
      else ts
    end // end of [list_cons]
  | list_nil () => let
      val () = flag := flag + 1 in list_cons (t0, list_nil)
    end // end of [list_nil]
// end of [tempset_insert]

(* ****** ****** *)

implement tempset_union (ts1, ts2) = let
  var flag: int = 0 in tempset_union_flag (ts1, ts2, flag)
end // end of [tempset_union]

implement tempset_union_flag
  (ts1, ts2, flag) = case+ (ts1, ts2) of
  | (list_cons (t1, ts1_tl), list_cons (t2, ts2_tl)) => let
      val sgn = $TL.compare_temp_temp (t2, t1)
    in
      if sgn < 0 then let
        val () =  flag := flag + 1 in
        list_cons (t2, tempset_union_flag (ts1, ts2_tl, flag))
      end else if sgn > 0 then
        list_cons (t1, tempset_union_flag (ts1_tl, ts2, flag))
      else begin
        list_cons (t1, tempset_union_flag (ts1_tl, ts2_tl, flag))
      end // end of [if]
    end (* end of [list_cons, list_cons] *)
  | (_, list_nil ()) => ts1
  | (list_nil (), _) => (flag := flag + 1; ts2)
// end of [tempset_union_flag]

(* ****** ****** *)

implement tempset_diff (ts1, ts2) = case+ (ts1, ts2) of
  | (list_cons (t1, ts1_tl), list_cons (t2, ts2_tl)) => let
      val sgn = $TL.compare_temp_temp (t2, t1)
    in
      if sgn < 0 then tempset_diff (ts1, ts2_tl)
      else if sgn > 0 then list_cons (t1, tempset_diff (ts1_tl, ts2))
      else tempset_diff (ts1_tl, ts2_tl)
    end // end of [list_cons, list_cons]
  | (list_nil _, _) => list_nil ()
  | (_, list_nil _) => ts1
// end of [tempset_diff]

(* ****** ****** *)

(* end of [tempset.dats] *)
