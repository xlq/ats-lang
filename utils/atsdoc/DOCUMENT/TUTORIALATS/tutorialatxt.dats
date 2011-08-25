(*
**
** Author: Hongwei Xi (gmhwxi AT gmail DOT com)
** Time: August, 2011
**
*)
//
// For write the TUTORIALATS book
//
staload UN = "prelude/SATS/unsafe.sats"
//
staload
STDIO = "libc/SATS/stdio.sats"
staload TIME = "libc/SATS/time.sats"
//
dynload "libatsdoc/dynloadall.dats"
//
staload "libatsdoc/SATS/atsdoc_text.sats"
//
val LT = "<"
val LTSLASH = "</"
val GT = ">"

val COMMENTopn = TEXTstrcst"<!--"
and COMMENTcls = TEXTstrcst("-->")

fun xmltagging (
  tag: string, x: string
) : text = let
  val _opn = TEXTappstr3 (LT, tag, GT)
  val _clo = TEXTappstr3 (LTSLASH, tag, GT)
in
  TEXTapptxt3 (_opn, TEXTstrsub(x), _clo)
end // end of [xmltagging]
//
fun id(x) = TEXTstrcst(x)
//
macdef title (x) = xmltagging ("title", ,(x))
//
macdef emph (x) = xmltagging ("emphasis", ,(x))
macdef para (x) = xmltagging ("para", ,(x))
//
macdef code (x) = xmltagging ("code", ,(x))
//
macdef command (x) = xmltagging ("command", ,(x))
//
macdef LI (x) = xmltagging ("listitem", ,(x))
//
fun itemizedlist
  (xs: textlst): text = let
  val opn = TEXTstrcst "<itemizedlist>\n"
  val cls = TEXTstrcst "\n</itemizedlist>"
in
  TEXTapptxt3 (opn, TEXTcontxt (xs), cls)
end
//
local
val ATSCODEopn = "<informalexample><programlisting><![CDATA["
val ATSCODEcls = "]]></programlisting></informalexample>"
in
fun atscode
  (x: string): text = TEXTappstr3 (ATSCODEopn, x, ATSCODEcls)
(*
fun atscode2xmls (x: string): text = atscode2xml_strcode (0, x)
fun atscode2xmld (x: string): text = atscode2xml_strcode (1, x)
*)
end // end of [local]
//
(* ****** ****** *)

fun timestamp
  (): text = let
  var time = $TIME.time_get ()
  val (fpf | x) = $TIME.ctime (time)
  val x1 = sprintf ("%s", @($UN.castvwtp1(x)))
  prval () = fpf (x)
  val x1 = string_of_strptr (x1)
in
  TEXTstrcst (x1)
end // end of [val]

(* ****** ****** *)

fun ignore (x: string): text = TEXTnil ()

fun comment (x: string): text =
  TEXTapptxt3 (COMMENTopn, TEXTstrsub(x), COMMENTcls)
// end of [comment]

(* ****** ****** *)

// (*
#define MYDOCROOT "http://www.ats-lang.org/DOCUMENT"
// *)
(*
#define MYDOCROOT "http://www.cs.bu.edu/~hwxi/ATS/DOCUMENT"
*)

fun mydoclink (
  codepath: string, linkname: string
) : text = let
  val res = sprintf (
    "<ulink url=\"%s/TUTORIALATS/DOC/%s\">%s</ulink>", @(MYDOCROOT, codepath, linkname)
  ) // end of [val]
  val res = string_of_strptr (res)
in
  TEXTstrcst (res)
end // end of [mydoclink]

fun myatsdoclink (
  codepath: string, linkname: string
) : text = let
  val res = sprintf (
    "<ulink url=\"%s/ANAIRIATS/%s\">%s</ulink>", @(MYDOCROOT, codepath, linkname)
  ) // end of [val]
  val res = string_of_strptr (res)
in
  TEXTstrcst (res)
end // end of [myatsdoclink]

(* ****** ****** *)

(* end of [tutorialatxt.dats] *)
