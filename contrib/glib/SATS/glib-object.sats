(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: April, 2010
//

(* ****** ****** *)

%{#
#include "contrib/glib/CATS/glib-object.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no static loading at run-time

(* ****** ****** *)

staload GLIB = "contrib/glib/SATS/glib.sats"
stadef gboolean = $GLIB.gboolean
stadef gint = $GLIB.gint
stadef guint = $GLIB.guint
stadef gpointer = $GLIB.gpointer

(* ****** ****** *)

absviewt@ype
GObject_vt (c:cls) = $extype "GObject"
// abst@ype GObjectClass = $extype "GObjectClass"

absviewt@ype
GInitiallyUnowned_vt (c:cls) = $extype "GInitiallyUnowned"
// abst@ype GInitiallyUnownedClass = $extype "GInitiallyUnownedClass"

(* ****** ****** *)

objcls GObject = { super: (*none*) }
absviewtype gobjptr (c:cls, l:addr) // gobject pointer

//
// HX-2010-04-13: this is unsafe but I cannot find a better means ...
//
castfn g_object_vref {c:cls} {l:addr} // vitural reference
  (x: !gobjptr (c, l)):<> (gobjptr (c, l) -<lin,prf> void | gobjptr (c, l))
// end of [g_object_vref]

(* ****** ****** *)

fun g_object_is_null
  {c:cls} {l:addr} (x: !gobjptr (c, l)): bool (l == null)
  = "atspre_ptr_is_null"
// end of [g_object_is_null]

fun g_object_isnot_null
  {c:cls} {l:addr} (x: !gobjptr (c, l)): bool (l > null)
  = "atspre_ptr_isnot_null"
// end of [g_object_is_null]

(* ****** ****** *)

abstype GCallback // = () -<fun1> void
castfn G_CALLBACK {a:type} (x: a): GCallback // unfortunately ...

(* ****** ****** *)

#include "contrib/glib/SATS/gobject/gsignal.sats"
#include "contrib/glib/SATS/gobject/gobject.sats"

(* ****** ****** *)

(* end of [glib-object.sats] *)

////

gobject:
gboxed.h    gobjectalias.h    gtype.h	     gvaluecollector.h
gclosure.h  gparam.h	      gtypemodule.h  gvaluetypes.h
genums.h    gparamspecs.h     gtypeplugin.h  stamp-gmarshal.h
gmarshal.h  gsignal.h	      gvalue.h
gobject.h   gsourceclosure.h  gvaluearray.h
