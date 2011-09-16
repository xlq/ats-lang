(*
**
** Author: Hongwei Xi (gmhwxi AT gmail DOT com)
** Time: August, 2011
**
*)
(* ****** ****** *)
//
// For write the TUTORIALATS book
//
staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"
//
(* ****** ****** *)

#include "utils/atsdoc/HATS/docbookatxt.hats"

(* ****** ****** *)

macdef filename(x) =
  xmltagging ("filename", ,(x)) // italic
// end of [filename]

(* ****** ****** *)
//
macdef LI (x) = xmltagging ("listitem", ,(x))
//
fun itemizedlist
  (xs: textlst): text = let
  val opn = TEXTstrcst "<itemizedlist>\n"
  val cls = TEXTstrcst "\n</itemizedlist>"
in
  TEXTapptxt3 (opn, TEXTcontxtsep (xs, TEXTnewline), cls)
end
//
(* ****** ****** *)

#define MYDOCROOT "http://www.ats-lang.org/DOCUMENT"
(*
#define MYDOCROOT "http://www.cs.bu.edu/~hwxi/ATS/DOCUMENT"
*)

(* ****** ****** *)

fun mydoclink (
  path: string, linkname: string
) : text = let
  val res = sprintf (
    "<ulink url=\"%s/TUTORIALATS/%s\">%s</ulink>", @(MYDOCROOT, path, linkname)
  ) // end of [val]
  val res = string_of_strptr (res)
in
  TEXTstrcst (res)
end // end of [mydoclink]

fun mycodelink (
  path: string, linkname: string
) : text = let
  val res = sprintf (
    "<ulink url=\"%s/TUTORIALATS/CODE/%s\">%s</ulink>", @(MYDOCROOT, path, linkname)
  ) // end of [val]
  val res = string_of_strptr (res)
in
  TEXTstrcst (res)
end // end of [mydoclink]

fun myatsdoclink (
  path: string, linkname: string
) : text = let
  val res = sprintf (
    "<ulink url=\"%s/ANAIRIATS/%s\">%s</ulink>", @(MYDOCROOT, path, linkname)
  ) // end of [val]
  val res = string_of_strptr (res)
in
  TEXTstrcst (res)
end // end of [myatsdoclink]

(* ****** ****** *)

local

val theCodeLst = ref<textlst> (list_nil)

in // in of [local]

fun theCodeLst_add (x: text) =
  !theCodeLst := list_cons (x, !theCodeLst)

fun theCodeLst_get (): textlst = let
  val xs = list_reverse (!theCodeLst) in list_of_list_vt (xs)
end // end of [theCodeLst_get]

fun fprint_theCodeLst
  (out: FILEref): void = let
  fun loop (xs: textlst, i: int):<cloref1> void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = if i > 0 then fprint_newline (out)
        val () = fprint_text (out, x)
      in
        loop (xs, i+1)
      end // end of [list_cons]
    | list_nil () => ()
in
  loop (theCodeLst_get (),  0)
end // end of [fprint_theCodeLst]

end // end of [local]

(* ****** ****** *)

fn atscode_extract
  (x: string): text = let
  val () = theCodeLst_add (TEXTstrcst (x)) in atscode (x)
end // end of [atscode_extract]

(* ****** ****** *)

(* end of [tutorialatxt.dats] *)
