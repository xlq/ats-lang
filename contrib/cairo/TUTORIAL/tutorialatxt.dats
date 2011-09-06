(*
**
** Author: Hongwei Xi (gmhwxi AT gmail DOT com)
** Time: August, 2011
**
*)
(* ****** ****** *)
//
// For write the ATS/Cairo tutorial
//
staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"
//
(* ****** ****** *)

#include "utils/atsdoc/DATS/docbookatxt.dats"

(* ****** ****** *)
//
#define s2s string_of_strptr
//
macdef strcst (x) = TEXTstrcst ,(x)
macdef strsub (x) = TEXTstrsub ,(x)
//
fun strcst_of_strptr (x: strptr1): text = TEXTstrcst ((s2s)x)
fun strsub_of_strptr (x: strptr1): text = TEXTstrsub ((s2s)x)
//
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

fun filename (x: string) = TEXTstrcst (x)

(* ****** ****** *)

#define MYDOCROOT
"http://www.ats-lang.org/DOCUMENT/ATSCAIRO"
#define MYCODEROOT
"http://www.ats-lang.org/DOCUMENT/ATSCAIRO/CODE"
#define MYIMAGEROOT
"http://www.ats-lang.org/DOCUMENT/ATSCAIRO/IMAGE"
(*
#define MYIMAGEROOT "IMAGE" // for generation pdf version
*)

fun MYDOCROOTget () = TEXTstrcst (MYDOCROOT)
fun MYCODEROOTget () = TEXTstrcst (MYCODEROOT)
fun MYIMAGEROOTget () = TEXTstrcst (MYIMAGEROOT)

(* ****** ****** *)

#define ATSLANGSVNROOT
"https://ats-lang.svn.sourceforge.net/svnroot/ats-lang/trunk"

fun ATSLANGSVNROOTget () = TEXTstrcst (ATSLANGSVNROOT)

(* ****** ****** *)

fun ulink (link: string, name: string): text =
  strcst_of_strptr (sprintf ("<ulink url=\"%s\">%s</ulink>", @(link, name)))
// end of [ulink]

fun ulink1 (link: string, name: string): text =
  strsub_of_strptr (sprintf ("<ulink url=\"%s\">%s</ulink>", @(link, name)))
// end of [ulink1]

(* ****** ****** *)

fun mydoclink (
  path: string, linkname: string
) : text = let
  val res = sprintf (
    "<ulink url=\"%s/%s\">%s</ulink>", @(MYDOCROOT, path, linkname)
  ) // end of [val]
  val res = string_of_strptr (res)
in
  TEXTstrcst (res)
end // end of [mydoclink]

fun mycodelink (
  path: string, linkname: string
) : text = let
  val res = sprintf (
    "<ulink url=\"%s/%s\">%s</ulink>", @(MYCODEROOT, path, linkname)
  ) // end of [val]
  val res = string_of_strptr (res)
in
  TEXTstrcst (res)
end // end of [mycodelink]

fun myimagelink (
  path: string, linkname: string
) : text = let
  val res = sprintf (
    "<ulink url=\"%s/%s\">%s</ulink>", @(MYIMAGEROOT, path, linkname)
  ) // end of [val]
  val res = string_of_strptr (res)
in
  TEXTstrcst (res)
end // end of [myimagelink]

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
