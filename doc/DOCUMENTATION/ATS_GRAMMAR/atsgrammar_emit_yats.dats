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
staload _(*anon*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

staload "atsgrammar.sats"

(* ****** ****** *)

fun emit_sym_term
  (out: FILEref, x: symbol): void = let
  val name = symbol_get_name (x)
  val tname = symbol_get_tyname (x)
  val () = fprint_string (out, "%token ")
  val () = if
    tyname_is_some (tname) then let
    val () = fprint_string (out, "<")
    val () = fprint_tyname (out, tname)
    val () = fprint_string (out, "> ")
  in
    // nothing
  end // end of [val]
  val () = fprint_string (out, name)
  val () = fprint_newline (out)
in
  // nothing
end // end of [emit_sym_term]

fun emit_symall_term (
  out: FILEref, xs: !symlst_vt
) : void = let
  fun loop (out: FILEref, xs: !symlst_vt): void =
    case+ xs of
    | list_vt_cons (x, !p_xs1) => let
        val isnt = symbol_get_nonterm (x)
        val () = if isnt then () else emit_sym_term (out, x)
        val () = loop (out, !p_xs1)
      in
        fold@ (xs)
      end // end of [list_vt_cons]
    | list_vt_nil () => (fold@ xs) // end of [list_vt_nil]
  // end of [loop]
in
  loop (out, xs)
end // end of [emit_symall_term]

(* ****** ****** *)

fun emit_sym_nonterm
  (out: FILEref, x: symbol): void = let
  val name = symbol_get_name (x)
  val tname = symbol_get_tyname (x)
  val () = fprint_string (out, "%type ")
  val () = if
    tyname_is_some (tname) then let
    val () = fprint_string (out, "<")
    val () = fprint_tyname (out, tname)
    val () = fprint_string (out, "> ")
  in
    // nothing
  end // end of [val]
  val () = fprint_string (out, name)
  val () = fprint_newline (out)
in
  // nothing
end // end of [emit_sym_nonterm]

fun emit_symall_nonterm (
  out: FILEref, xs: !symlst_vt
) : void = let
  fun loop (out: FILEref, xs: !symlst_vt): void =
    case+ xs of
    | list_vt_cons (x, !p_xs1) => let
        val isnt = symbol_get_nonterm (x)
        val () = if isnt then emit_sym_nonterm (out, x) else ()
        val () = loop (out, !p_xs1)
      in
        fold@ (xs)
      end // end of [list_vt_cons]
    | list_vt_nil () => (fold@ xs) // end of [list_vt_nil]
  // end of [loop]
in
  loop (out, xs)
end // end of [emit_symall_nonterm]

(* ****** ****** *)

fun emit_symreg
  (out: FILEref, r: symreg): void = case+ r of
  | SYMREGlit (x) => fprint_string (out, symbol_get_name (x))
  | _ => fprint_string (out, "(ERROR)")
// end of [emit_symreg]

fun emit_grmrule (
  out: FILEref, gr: grmrule
) : void = let
  fun loop (
    out: FILEref, xs: symreglst, i: int
  ) : void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = if (i > 0) then fprint_string (out, " ")
        val () = emit_symreg (out, x)
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
end // end of [emit_grmrule]

(* ****** ****** *)

fun emit_sym_defn (
  out: FILEref, x: symbol
) : void = let
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
          val () = emit_grmrule (out, gr)
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
end // end of [emit_sym_defn]

(* ****** ****** *)

fun emit_symall_defn (
  out: FILEref, xs: !symlst_vt
) : void = let
  fun loop (out: FILEref, xs: !symlst_vt): void =
    case+ xs of
    | list_vt_cons (x, !p_xs1) => let
        val isnt = symbol_get_nonterm (x)
        val () = if isnt then emit_sym_defn (out, x)
        val () = loop (out, !p_xs1)
      in
        fold@ (xs)
      end // end of [list_vt_cons]
    | list_vt_nil () => fold@ (xs) // end of [list_vt_nil]
  // end of [loop]
in
  loop (out, xs)
end // end of [emit_symall_defn]

(* ****** ****** *)

implement
emit_yats (out) = let
  val xs = theSymlst_get ()
  val xs = list_reverse (xs)
  val () = emit_symall_term (out, xs)
  val () = fprint_string (out, "\n/* ****** ****** */\n\n")
  val () = emit_symall_nonterm (out, xs)
  val () = fprint_string (out, "\n/* ****** ****** */\n\n")
  val () = emit_symall_defn (out, xs)
in
  list_vt_free (xs)
end // end of [emit_yats]

(* ****** ****** *)

(* end of [atsgrammar_emit_yats.dats] *)
