(*
**
** For documenting the grammar of ATS
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Sylvain Nahas (sylvain.nahas AT googlemail DOT com)
**
** Time: November, 2010
**
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"

(* ****** ****** *)

staload "atsgrammar.sats"

(* ****** ****** *)

fun symbol_get_descname
  (x: symbol): string = let
  val fname = symbol_get_fullname (x)
in
  if stropt_is_some (fname)
    then stropt_unsome (fname) else symbol_get_name (x)
  // end of [if]
end // end of [symbol_get_descname]

fun emit_symreg_desc (
  out: FILEref, r: symreg
) : void = begin
  case+ r of
  | SYMREGlit (x) => let
      val fname = symbol_get_descname (x)
    in
      fprintf (out, "%s", @(fname))
    end // end of [SYMREGlit]
  | SYMREGseq (x1, x2) => let
      val fname1 = symbol_get_descname (x1)
      and fname2 = symbol_get_descname (x2)
    in
      fprintf (out, "(%s , %s)", @(fname1, fname2))
    end // end of [SYMREGseq]
  | SYMREGalt (x1, x2) => let
      val fname1 = symbol_get_descname (x1)
      and fname2 = symbol_get_descname (x2)
    in
      fprintf (out, "(%s | %s)", @(fname1, fname2))
    end // end of [SYMREGalt]
  | SYMREGopt (x) => let
      val fname = symbol_get_descname (x)
    in
      fprintf (out, "[%s]", @(fname))
    end // end of [SYMREGopt]
  | SYMREGstar (x) => let
      val fname = symbol_get_descname (x)
    in
      fprintf (out, "{%s}", @(fname))
    end // end of [SYMREGstar]
  | SYMREGplus (x) => let
      val fname = symbol_get_descname (x)
    in
      fprintf (out, "{%s}+", @(fname))
    end // end of [SYMREGplus]
end // end of [emit_symreg_desc]

fun emit_grmrule_desc (
  out: FILEref, gr: grmrule
) : void = let
  fun loop (
    out: FILEref, xs: symreglst, i: int
  ) : void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = if (i > 0) then fprint_string (out, " ")
        val () = emit_symreg_desc (out, x)
      in
        loop (out, xs, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
  val xs = grmrule_get_symreglst (gr)
in
  case+ xs of
  | list_cons _ => loop (out, xs, 0)
  | list_nil () => fprint_string (out, "/*(empty)*/")
end // end of [emit_grmrule_desc]

(* ****** ****** *)

implement
emit_symdef_desc (out, x) = let
//
  fun loop (
    out: FILEref, grs: grmrulelst, i: &int
  ) : void =
    case+ grs of
    | list_cons (gr, grs) => let
        val ismrgd = grmrule_get_merged (gr)
        val () = if ismrgd = 0 then let
          val () = i := i + 1
          val () = fprintf (out, "  | ", @())
          val () = emit_grmrule_desc (out, gr)
          val () = fprint_newline (out)
        in
          // nothing
        end // end of [if]
      in
        loop (out, grs, i)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
//
  val fname = symbol_get_descname (x)
  val () = fprintf (out, "%s\n", @(fname))
  var i: int = 0
  val () = loop (out, symbol_get_grmrulelst (x), i)
  val () = fprintf (out, "; /* %s */\n\n", @(fname))
//
in
  // nothing  
end // end of [emit_symdef_desc]

(* ****** ****** *)

implement
emit_symdefall_desc (out) = let
  fun loop (out: FILEref, xs: symlst_vt): void =
    case+ xs of
    | ~list_vt_cons (x, xs) => let
        val isnt = symbol_get_nonterm (x)
        val () = if isnt then emit_symdef_desc (out, x)
      in
        loop (out, xs)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => () // end of [list_vt_nil]
  // end of [loop]
in
  loop (out, list_reverse (theSymlst_get ()))
end // end of [emit_symdefall_desc]

(* ****** ****** *)

(* end of [atsgrammar_emit_desc.dats] *)
