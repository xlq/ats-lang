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

fun emit_symreg_yats
  (out: FILEref, r: symreg): void = case+ r of
  | SYMREGlit (x) => fprint_string (out, symbol_get_name (x))
  | _ => fprint_string (out, "(ERROR)")
// end of [emit_symreg_yats]

fun emit_grmrule_yats (
  out: FILEref, gr: grmrule
) : void = let
  fun loop (
    out: FILEref, xs: symreglst, i: int
  ) : void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = if (i > 0) then fprint_string (out, " ")
        val () = emit_symreg_yats (out, x)
      in
        loop (out, xs, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
  val xs = grmrule_get_symreglst (gr)
  val () = (case+ xs of
    | list_cons _ => loop (out, xs, 0)
    | list_nil () => fprint_string (out, "/*(empty)*/")
  ) : void // end of [val]
  val action = grmrule_get_action (gr)
  val () = if
    stropt_is_some (action) then let
    val action = stropt_unsome (action)
  in
    fprintf (out, "  %s", @(action))
  end // end of [val]
in
  // nothing
end // end of [emit_grmrule_yats]

(* ****** ****** *)

implement
emit_symdef_yats (out, x) = let
//
  fun loop (
    out: FILEref, grs: grmrulelst, i: &int
  ) : void =
    case+ grs of
    | list_cons (gr, grs) => let
        val knd = grmrule_get_kind (gr)
        val () = if knd = 0 then let
          val c = (
            if i = 0 then ':' else '|'
          ) : char // end of [val]
          val () = i := i+1
          val () = fprintf (out, "  %c ", @(c))
          val () = emit_grmrule_yats (out, gr)
          val () = fprint_newline (out)
        in
          // nothing
        end // end of [val]
      in
        loop (out, grs, i)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
//
  val name = symbol_get_name (x)
  val () = fprintf (out, "%s\n", @(name))
  var i: int = 0
  val () = loop (out, symbol_get_grmrulelst (x), i)
  val () = fprintf (out, "; /* %s */\n\n", @(name))
//
in
  // nothing  
end // end of [emit_symdef_yats]

(* ****** ****** *)

implement
emit_symdefall_yats (out) = let
  fun loop (out: FILEref, xs: symlst_vt): void =
    case+ xs of
    | ~list_vt_cons (x, xs) => let
        val isnt = symbol_get_nonterm (x)
        val () = if isnt then emit_symdef_yats (out, x)
      in
        loop (out, xs)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => () // end of [list_vt_nil]
  // end of [loop]
in
  loop (out, list_reverse (theSymlst_get ()))
end // end of [emit_symdefall_yats]

(* ****** ****** *)

(* end of [atsgrammar_emit_yats.dats] *)
