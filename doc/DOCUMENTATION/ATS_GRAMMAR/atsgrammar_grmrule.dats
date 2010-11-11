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
staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "atsgrammar.sats"

(* ****** ****** *)

macdef list_sing (x) = list_cons (,(x), list_nil)

(* ****** ****** *)

extern
fun grmrule_make_symlst (xs: symlst): grmrule

extern
fun grmrule_get_symreglst (gr: grmrule): symreglst

(* ****** ****** *)

local

assume grmrule = List (symreg)

in // in of [local]

implement
grmrule_make_symlst (xs) = let
  val xs =
    list_map_fun<symbol,symreg> (xs, lam x =<1> SYMREGlit (x))
  // end of [val]
in
  list_of_list_vt (xs)
end // end of [grmrule_make_symlst]

implement grmrule_get_symreglst (gr) = gr

end // end of [local]

(* ****** ****** *)

val theGrmrulelst = ref<grmrulelst_vt> (list_vt_nil)

(* ****** ****** *)

implement
theGrmrulelst_get () = let
  val (vbox pf | p) = ref_get_view_ptr (theGrmrulelst)
  val xs = !p
  val () = !p := list_vt_nil ()
in
  xs
end // end of [theGrmrulelst_get]

(* ****** ****** *)

implement
theGrmrulelst_add (x) = let
  val (vbox pf | p) = ref_get_view_ptr (theGrmrulelst)
in
  !p := list_vt_cons (x, !p)
end // end of [theGrmrulelst_add]

(* ****** ****** *)

implement
grmrule_append_empty () =
  grmrule_append_symlst (list_nil ())
// end of [grmrule_append_empty]

(* ****** ****** *)

implement
grmrule_append_symbol (x) =
  grmrule_append_symlst (list_sing (x))
// end of [grmrule_append_symbol]

(* ****** ****** *)

implement
grmrule_append_symlst (xs) = let
  val gr = grmrule_make_symlst (xs)
in
  theGrmrulelst_add (gr)
end // end of [grmrule_append_symbol]

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
in
  case+ xs of
  | list_cons _ => loop (out, xs, 0)
  | list_nil () => fprint_string (out, "/*(empty)*/")
end // end of [emit_grmrule_yats]

(* ****** ****** *)

implement
emit_symdef_yats (out, x) = let
//
  fun loop (
    out: FILEref, grs: grmrulelst, i: int
  ) : void =
    case+ grs of
    | list_cons (gr, grs) => let
        val c = (
          if i = 0 then ':' else '|'
        ) : char // end of [val]
        val () = fprintf (out, "  %c ", @(c))
        val () = emit_grmrule_yats (out, gr)
        val () = fprint_newline (out)
      in
        loop (out, grs, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
//
  val name = symbol_get_name (x)
  val () = fprintf (out, "%s\n", @(name))
  val () = loop (out, symbol_get_grmrulelst (x), 0)
  val () = fprintf (out, "; /* %s */\n\n", @(name))
//
in
  // nothing  
end // end of [emit_symdef_yats]

(* ****** ****** *)

(* end of [atsgrammar_grmrule.dats] *)
