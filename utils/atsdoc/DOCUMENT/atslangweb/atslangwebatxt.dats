(*
**
** Author: Hongwei Xi (gmhwxi AT gmail DOT com)
** Time: August, 2011
**
*)
//
staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"
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
staload _(*anon*) = "libatsdoc/DATS/atsdoc_text.dats"
//
(* ****** ****** *)

#include "atslangweb_params.hats"

(* ****** ****** *)

#define s2s string_of_strptr

(* ****** ****** *)

fun ignore (x: string) = TEXTnil ()
fun ignoretxt (x: text) = TEXTnil ()

(* ****** ****** *)

macdef strcst (x) = TEXTstrcst ,(x)
macdef strsub (x) = TEXTstrsub ,(x)

fun strcst_of_strptr (x: strptr1): text = TEXTstrcst ((s2s)x)
fun strsub_of_strptr (x: strptr1): text = TEXTstrsub ((s2s)x)

(* ****** ****** *)

val LT = "<"
val LTSLASH = "</"
val GT = ">"

val TEXTnewline = TEXTstrcst"\n"
val COMMENTopn = TEXTstrcst"<!--"
and COMMENTcls = TEXTstrcst("-->")

fn xmltagging (
  tag: string, x: string
) : text = let
  val _opn = TEXTappstr3 (LT, tag, GT)
  val _clo = TEXTappstr3 (LTSLASH, tag, GT)
in
  TEXTapptxt3 (_opn, TEXTstrsub(x), _clo)
end // end of [xmltagging]

(* ****** ****** *)

macdef head (x) = xmltagging ("HEAD", ,(x)) // <HEAD> ... </HEAD>
macdef title (x) = xmltagging ("TITLE", ,(x)) // <TITLE> ... </TITLE>

(* ****** ****** *)

macdef emph (x) = xmltagging ("I", ,(x)) // <I> ... </I>
macdef para (x) = xmltagging ("P", ,(x)) // <P> ... </P>
macdef filename(x) = xmltagging ("U", ,(x)) // <U> ... </U>
macdef textpre(x) = xmltagging ("PRE", ,(x)) // <PRE> ... </PRE>
macdef command(x) = xmltagging ("PRE", ,(x)) // <PRE> ... </PRE>

(* ****** ****** *)

local

val COMMENTopn = TEXTstrcst"<!--"
and COMMENTcls = TEXTstrcst("-->")

in // in of [local]

fun comment (x: string): text =
  TEXTapptxt3 (COMMENTopn, TEXTstrsub(x), COMMENTcls)
// end of [comment]

end // end of [local]

(* ****** ****** *)

fn HR (sz: int) =
  strcst_of_strptr (sprintf ("<HR SIZE=%i></HR>", @(sz)))
// end of [HR]

(* ****** ****** *)

fun uid (id: string, name: string): text =
  strcst_of_strptr (sprintf ("<a id=\"%s\">%s</a>", @(id, name)))
// end of [uid]

fun ulink (link: string, name: string): text =
  strcst_of_strptr (sprintf ("<a href=\"%s\">%s</a>", @(link, name)))
// end of [ulink]

fun ulink1 (link: string, name: string): text =
  strsub_of_strptr (sprintf ("<a href=\"%s\">%s</a>", @(link, name)))
// end of [ulink1]

(* ****** ****** *)

fun ATSLANGWEBROOTget (): text = TEXTstrcst (ATSLANGWEBROOT)

val ATSLANGWEBHOME: text = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/\">Home</a>", @(ATSLANGWEBROOT))
}
val ATSLANGWEBDOWNLOAD: text = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/DOWNLOAD/\">Download</a>", @(ATSLANGWEBROOT))
}
val ATSLANGWEBDOCUMENT: text = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/DOCUMENT/\">Documentation</a>", @(ATSLANGWEBROOT))
}
val ATSLANGWEBLIBRARY: text = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/LIBRARY/\">Libraries</a>", @(ATSLANGWEBROOT))
}
val ATSLANGWEBRESOURCE: text = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/RESOURCE/\">Resources</a>", @(ATSLANGWEBROOT))
}
val ATSLANGWEBEXAMPLE: text = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/EXAMPLE/\">Examples</a>", @(ATSLANGWEBROOT))
}
val ATSLANGWEBIMPLEMENT: text = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/IMPLEMENT/\">Implementations</a>", @(ATSLANGWEBROOT))
}
val ATSLANGWEBPAPER: text = strcst ((s2s)res) where {
  val res = sprintf ("<a href=\"%s/PAPER/\">Papers</a>", @(ATSLANGWEBROOT))
}

#ifndef ISTEMP
#define ISTEMP 0
#endif
#if(ISTEMP==0)
val () = theTextMap_insert_str ("ATSLANGWEBHOME", ATSLANGWEBHOME)
val () = theTextMap_insert_str ("ATSLANGWEBDOWNLOAD", ATSLANGWEBDOWNLOAD)
val () = theTextMap_insert_str ("ATSLANGWEBDOCUMENT", ATSLANGWEBDOCUMENT)
val () = theTextMap_insert_str ("ATSLANGWEBLIBRARY", ATSLANGWEBLIBRARY)
val () = theTextMap_insert_str ("ATSLANGWEBRESOURCE", ATSLANGWEBRESOURCE)
val () = theTextMap_insert_str ("ATSLANGWEBEXAMPLE", ATSLANGWEBEXAMPLE)
val () = theTextMap_insert_str ("ATSLANGWEBIMPLEMENT", ATSLANGWEBIMPLEMENT)
val () = theTextMap_insert_str ("ATSLANGWEBPAPER", ATSLANGWEBPAPER)
#endif

(* ****** ****** *)

local

fn make_ahref (
  link: string, name: string
) : string = let
  val res = sprintf ("<a href=\"%s\">%s</a>", @(link, name))
in
  (s2s)res
end // end of [make_ahref]

fn subpage_ahref
  (flag: int, link: string, name: string): string = let
in
  if flag > 0 then let
    val name = sprintf ("<strong>%s</strong>", @(name))
  in
    (s2s)name // name only
  end else 
    make_ahref (link, name)
   // end of [if]
end // end of [subpage_ahref]

val root = ATSLANGWEBROOT

in // in of [local]

fn HOME_ahref
  (flag: int): string = let
  val link = sprintf ("%s/", @(root))
  val link = (s2s)link
in
  subpage_ahref (flag, link, "Home")
end // end of [HOME_ahref]

fn DOWNLOAD_ahref
  (flag: int): string = let
  val link = sprintf ("%s/%s", @(root, "DOWNLOAD"))
  val link = (s2s)link
in
  subpage_ahref (flag, link, "Download")
end // end of [DOWNLOAD_ahref]

fn DOCUMENT_ahref
  (flag: int): string = let
  val link = sprintf ("%s/%s", @(root, "DOCUMENT"))
  val link = (s2s)link
in
  subpage_ahref (flag, link, "Documentation")
end // end of [DOCUMENT_ahref]

fn LIBRARY_ahref
  (flag: int): string = let
  val link = sprintf ("%s/%s", @(root, "LIBRARY"))
  val link = (s2s)link
in
  subpage_ahref (flag, link, "Libraries")
end // end of [LIBRARY_ahref]

fn RESOURCE_ahref
  (flag: int): string = let
  val link = sprintf ("%s/%s", @(root, "RESOURCE"))
  val link = (s2s)link
in
  subpage_ahref (flag, link, "Resources")
end // end of [RESOURCE_ahref]

end // end of [local]

(* ****** ****** *)

fn mysitelinks (current: string) = let
//
  val flag = (if (current = "HOME") then 1 else 0): int
  val HOME = strcst (HOME_ahref (flag))
//
  val flag = (if (current = "DOWNLOAD") then 1 else 0): int
  val DOWNLOAD = strcst (DOWNLOAD_ahref (flag))
//
  val flag = (if (current = "DOCUMENT") then 1 else 0): int
  val DOCUMENT = strcst (DOCUMENT_ahref (flag))
//
  val flag = (if (current = "LIBRARY") then 1 else 0): int
  val LIBRARY = strcst (LIBRARY_ahref (flag))
//
  val flag = (if (current = "RESOURCE") then 1 else 0): int
  val RESOURCE = strcst (RESOURCE_ahref (flag))
//
  val xs = $lst {text} (HOME, DOWNLOAD, DOCUMENT, LIBRARY, RESOURCE)
//
  val sep = strcst ("<span class=\"separator\"> | </span>")
//
in
  TEXTcontxtsep (xs, sep)
end // end of [mysitelinks]

(* ****** ****** *)

(* end of [atslangwebatxt.dats] *)
