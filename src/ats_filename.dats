(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: July 2007

(* ****** ****** *)

(* ats_filename: handling the names of files *)

(* ****** ****** *)

%{^
#include <sys/stat.h>
%}

(* ****** ****** *)

staload Loc = "ats_location.sats"

(* ****** ****** *)

staload Sym = "ats_symbol.sats"
overload = with $Sym.eq_symbol_symbol
overload <> with $Sym.neq_symbol_symbol

// HX: this is now handled in [ats_main.dats] 
// dynload "ats_symbol.dats" // this file needs to be loaded first!!!

(* ****** ****** *)

staload "ats_filename.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

fn prerr_interror () = prerr "INTERNAL ERROR (ats_filename)"

(* ****** ****** *)

local

#include "prelude/params_system.hats"
#if OPERATING_SYSTEM_IS_UNIX_LIKE #then
//
val theDirsep: char = '/'
val theCurdir: string = "./"
val thePredir: string = "../"
//
#endif

in

//
// staload "libc/SATS/unistd.sats"
//
extern fun getcwd (): String = "atslib_getcwd"

implement theDirsep_get () = theDirsep
implement theCurdir_get () = theCurdir
implement thePredir_get () = thePredir


end // end of [local]

(* ****** ****** *)

#define THISFILENAME "ats_filename.dats"

implement filename_is_relative (name) = let
  val name = string1_of_string name
  fn aux {n,i:nat | i <= n}
    (name: string n, i: size_t i, dirsep: char): bool =
    if string_is_at_end (name, i) then true else name[i] <> dirsep
  // end of [aux]
  val dirsep = theDirsep_get ()
in
  aux (name, 0, dirsep)
end // [filename_is_relative]

%{^
//
static inline
ats_bool_type
ats_filename_is_exist (ats_ptr_type name) {
  struct stat st ;
  return stat ((char*)name, &st) ? ats_false_bool : ats_true_bool ;
} /* end of [ats_filename_is_exist] */
//
%} // end of [%{^]

(* ****** ****** *)

%{$

ats_ptr_type
ats_filename_append (
  ats_ptr_type dir, ats_ptr_type bas
) {
  int n1, n2, n ;
  char dirsep, *dirbas ;
//
  dirsep = ats_filename_theDirsep_get () ;
//
  n1 = strlen ((char*)dir) ;
  n2 = strlen ((char*)bas) ;
  n = n1 + n2 ;
  if (n1 > 0 && ((char*)dir)[n1-1] != dirsep) n += 1 ;
  dirbas = ATS_MALLOC (n + 1) ;
  memcpy (dirbas, dir, n1) ;
  if (n > n1 + n2) { dirbas[n1] = dirsep ; n1 += 1 ; }
  memcpy (dirbas + n1, bas, n2) ;
  dirbas[n] = '\000' ;

  return dirbas ;
} /* end of [ats_filename_append] */

%} // end of [%{$]

(* ****** ****** *)

typedef filename = '{
  filename_full= string, filename_full_sym= $Sym.symbol_t
} // end of [filename]

assume filename_t = filename

(* ****** ****** *)

implement filename_none = '{
  filename_full= "(none)"
, filename_full_sym= $Sym.symbol_empty
} // end of [filename_none]

implement filename_stdin = '{
  filename_full= "stdin"
, filename_full_sym= $Sym.symbol_STDIN
} // end of [filename_stdin]

(* ****** ****** *)

implement lt_filename_filename
  (x1, x2) = x1.filename_full < x2.filename_full
// end of [lt_filename_filename]

implement lte_filename_filename
  (x1, x2) = x1.filename_full <= x2.filename_full
// end of [lte_filename_filename]

implement gt_filename_filename
  (x1, x2) = x1.filename_full > x2.filename_full
// end of [gt_filename_filename]

implement gte_filename_filename
  (x1, x2) = x1.filename_full >= x2.filename_full
// end of [gte_filename_filename]

implement eq_filename_filename // symbol comparison
  (x1, x2) = x1.filename_full_sym = x2.filename_full_sym
// end of [eq_filename_filename]

implement neq_filename_filename // symbol comparison
  (x1, x2) = x1.filename_full_sym <> x2.filename_full_sym
// end of [neq_filename_filename]

implement compare_filename_filename (x1, x2) =
  compare (x1.filename_full, x2.filename_full)
// end of [compare_filename_filename]

(* ****** ****** *)

implement fprint_filename (pf | out, x) =
  fprint_string (pf | out, x.filename_full)

implement print_filename (x) = print_mac (fprint_filename, x)
implement prerr_filename (x) = prerr_mac (fprint_filename, x)

(* ****** ****** *)

// implement fprint_filename_base (pf | out, x) = (*implemented in C*)

implement print_filename_base (x) = print_mac (fprint_filename_base, x)
implement prerr_filename_base (x) = prerr_mac (fprint_filename_base, x)

(* ****** ****** *)

typedef path = string

staload "ats_list.sats"
staload _(*anon*) = "ats_list.dats"
fun path_normalize (s0: path): path = let
  fun loop1 {n0,i0:nat | i0 <= n0} (
      dirsep: char
    , s0: string n0, n0: size_t n0, i0: size_t i0, dirs: &List_vt string
    ) : void =
    if i0 < n0 then loop2 (dirsep, s0, n0, i0, i0, dirs) else ()
  and loop2 {n0,i0,i:nat | i0 < n0; i0 <= i; i <= n0} (
      dirsep: char
    , s0: string n0, n0: size_t n0, i0: size_t i0, i: size_t i, dirs: &List_vt string
    ) : void =
    if i < n0 then let
(*
      // empty
*)
    in
      if s0[i] <> dirsep then
        loop2 (dirsep, s0, n0, i0, i+1, dirs)
      else let
        val sbp = string_make_substring (s0, i0, i - i0 + 1)
        val dir = string1_of_strbuf (sbp) // this is a no-op cast
(*
        val () = begin
          print "filename_normalize: loop2: dir = "; print dir; print_newline ()
        end // end of [val]
*)
      in
        dirs := list_vt_cons (dir, dirs); loop1 (dirsep, s0, n0, i + 1, dirs)
      end // end of [if]
    end else let
      val sbp = string_make_substring (s0, i0, i - i0)
      val dir = string1_of_strbuf (sbp) // this is a no-op cast
(*
      val () = begin
        print "filename_normalize: loop2: dir = "; print dir; print_newline ()
      end // end of [val]
*)
    in
      dirs := list_vt_cons (dir, dirs)
    end // end of [if]
  // end of [loop1] and [loop2]
  fun dirs_process (
      curdir: string, predir: string
    , npre: Nat, dirs: List_vt string, res: List_vt string
    ) : List_vt string = case+ dirs of
    | ~list_vt_cons (dir, dirs) => begin
        if dir = curdir then
          dirs_process (curdir, predir, npre, dirs, res)
        else if dir = predir then
          dirs_process (curdir, predir, npre + 1, dirs, res)
        else begin
          if npre > 0 then begin
            dirs_process (curdir, predir, npre - 1, dirs, res)
          end else begin
            dirs_process (curdir, predir, 0, dirs, list_vt_cons (dir, res))
          end (* end of [if] *)
        end (* end of [if] *)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => loop (predir, npre, res) where {
        fun loop (
            predir: string, npre: Nat, res: List_vt string
          ) : List_vt string =
          if npre > 0 then loop (predir, npre - 1, list_vt_cons (predir, res))
          else res
        // end of [loop]
      } // end of [list_vt_nil]
//
  val dirsep = theDirsep_get ()
  val curdir = theCurdir_get () and predir = thePredir_get ()
//
  var dirs: List_vt string = list_vt_nil ()
  val s0 = string1_of_string s0; val n0 = string_length s0
  val () = loop1 (dirsep, s0, n0, 0, dirs)
  val () = dirs := dirs_process (curdir, predir, 0, dirs, list_vt_nil ())
  val fullname = stringlst_concat (__cast dirs) where {
    extern castfn __cast (x: !List_vt string): List string
  }
  val () = list_vt_free (dirs)
//
in
  string1_of_strbuf (fullname)
end // end of [path_normalize]

(* ****** ****** *)

typedef pathlst = List path

local

val the_pathlst = ref_make_elt<pathlst> (list_nil ())
val the_prepathlst = ref_make_elt<pathlst> (list_nil ())

in // in of [local]

fn the_pathlst_get (): pathlst = !the_pathlst
fn the_pathlst_reset () = !the_pathlst := list_nil ()

implement the_pathlst_pop () = begin
  case+ !the_pathlst of
  | list_cons (_, ps) => !the_pathlst := ps
  | list_nil () => begin
      prerr_interror ();
      prerr (": pathlst_pop: the_pathlst is empty."); prerr_newline ();
      exit (1)
    end // end of [list_nil]
end // end of [the_pathlst_pop]

implement the_pathlst_push (dirname) = let
  val dirname_full = (case+ 0 of
    | _ when filename_is_relative dirname => filename_append (getcwd (), dirname)
    | _ => dirname
  ) : string
  val dirname_full = path_normalize (dirname_full)
(*
  val () = begin
    print "the_pathlst_push: dirname = "; print dirname; print_newline ();
    print "the_pathlst_push: dirname_full = "; print dirname_full; print_newline ();
  end // end of [val]
*)
in
  !the_pathlst := list_cons (dirname_full, !the_pathlst)
end // end of [the_pathlst_push]

(* ****** ****** *)

fun the_prepathlst_get (): pathlst = !the_prepathlst

implement the_prepathlst_push (dirname) = let
  val () = if filename_is_relative dirname then begin
    prerr_interror ();
    // the directory name [dirname] is not absolute
    prerr (": the_prepathlst_push: dirname = "); prerr dirname; prerr_newline ();
    exit {void} (1)
  end // end of [val]
in
  !the_prepathlst := list_cons (dirname, !the_prepathlst)
end // end of [the_prepathlst_push]

end // end of [local]

(* ****** ****** *)

local

typedef filenamelst = List filename

val the_filename = ref_make_elt<filename> filename_none
val the_filenamelst = ref_make_elt<filenamelst> (list_nil ())

in // in of [local]

fn the_filename_reset (): void = !the_filename := filename_none
fn the_filenamelst_reset (): void = !the_filenamelst := list_nil ()

implement the_filename_get (): filename = !the_filename

val the_filenamelst_pop_err = lam () =<fun1> begin
  prerr_interror ();
  prerr (": the_filenamelst_pop: the_filenamelst is empty"); prerr_newline ();
  exit (1)
end // end of [the_filenamelst_pop_err]

implement the_filenamelst_pop () = begin
  case+ !the_filenamelst of
  | list_cons (f, fs) => begin
      !the_filename := f; !the_filenamelst := fs
    end // end of [list_cons]
  | list_nil () => the_filenamelst_pop_err ()
end // end of [the_filenamelst_pop]

implement the_filenamelst_push (f0) = let
  val fs = list_cons (!the_filename, !the_filenamelst)
in
  !the_filenamelst := fs; !the_filename := f0;
end // end of [the_filenamelst_push]

implement the_filenamelst_push_xit (loc0, f0) = let
(*
  val () = begin
    print "the_filenamelst_push: f0 = "; print f0; print_newline ()
  end // end of [val]
*)
  val loc0 = __cast loc0 where {
    extern castfn __cast (x: location_t): $Loc.location_t
  } // end of [val]
  val fs = list_cons (!the_filename, !the_filenamelst)
  val isexi = loop1 (fs, f0) where {
    fun loop1 (fs: filenamelst, f0: filename): bool =
      case+ fs of
      | list_cons (f, fs) => if f = f0 then true else loop1 (fs, f0)
      | list_nil () => false
    // end of [loop1]
  } // end of [val isexi]
  val () = if isexi then let
    val () = $Loc. prerr_location loc0
    val () = prerr (": error(0)")
    val () = prerr (": loading or including the file [");
    val () = prerr_filename (f0)
    val () = prerr ("] generates a looping trace that is given as follows:\n")
    val () = loop2 (fs, f0) where {
      fun loop2 (fs: filenamelst, f0: filename): void =
        case+ fs of
        | list_cons (f, fs) => let
            val () = prerr_filename f in if (f <> f0) then loop2 (fs, f0)
          end // end of [list_cons]
        | list_nil () => ()
    } // end of [val]
    val () = prerr_newline ()
  in
    exit (1) // compilation aborts
  end // end of [val]
in
  !the_filenamelst := fs; !the_filename := f0;
end // end of [the_filenamelst_push_xit]

end // end of [local]

(* ****** ****** *)

implement filename_full f = f.filename_full
implement filename_full_sym f = f.filename_full_sym

(* ****** ****** *)

implement filename_make_absolute (fullname) = let
  val fullname_id = fullname
  val fullname_sym = $Sym.symbol_make_string fullname
in '{
  filename_full= fullname
, filename_full_sym= fullname_sym
} end // end of [filename_make_absolute]

implement filenameopt_make (basename) = let
  val basename = string1_of_string basename
  fun aux_try (paths: pathlst, basename: String): Stropt =
    case+ paths of
    | list_cons (path, paths) => let
        val fullname = filename_append (path, basename)
        val fullname = string1_of_string fullname
(*
        val () = begin
          print "filenameopt_make: fullname = "; print fullname; print_newline ()
        end // end of [val]
*)
      in
        case+ 0 of
        | _ when filename_is_exist (fullname) => stropt_some fullname
        | _ => aux_try (paths, basename)
      end
    | list_nil () => stropt_none
  fun aux_relative (basename: String): Stropt = let
    val fullnameopt = aux_try (the_prepathlst_get (), basename)
  in
    case+ 0 of
    | _ when stropt_is_some fullnameopt => fullnameopt
    | _ when filename_is_exist basename => let
        val cwd = getcwd ()
        val fullname = filename_append (cwd, basename)
        val fullname = string1_of_string fullname
      in
        stropt_some fullname
      end
    | _ => aux_try (the_pathlst_get (), basename)
  end
  val fullnameopt = (case+ 0 of
    | _ when filename_is_relative basename => aux_relative basename
    | _ => begin
        if filename_is_exist basename then stropt_some basename else stropt_none
      end // end of [_]
  ) : Stropt // end of [val]
in
  if stropt_is_some fullnameopt then let
    val fullname = stropt_unsome fullnameopt
    val fullname = path_normalize fullname
  in
    Some_vt (filename_make_absolute fullname)
  end else begin
    None_vt ()
  end // end of [if]
end // end of [filenameopt_make]

(* ****** ****** *)

implement ats_filename_prerr () =
  prerr_filename (the_filename_get ())
// end of [ats_filename_prerr]

implement
ats_filename_initialize () = begin
  the_pathlst_reset (); the_filename_reset (); the_filenamelst_reset ()
end // end of [ats_filename_initialize]

(* ****** ****** *)

%{$
//
ats_void_type
ats_filename_fprint_filename_base
  (ats_ptr_type out, ats_ptr_type fil) {
  char dirsep, *name, *basename ;
  dirsep = ats_filename_theDirsep_get () ;
  name = (char*)ats_filename_full (fil) ;
  basename = strrchr (name, dirsep) ;

  if (basename) {
    ++basename ; fputs (basename, (FILE*)out) ;
  } else {
    fputs (name, (FILE*)out) ;
  } /* end of [if] */

  return ;
} /* end of [ats_filename_fprint_filename_base] */
//
%} // end of [%{$]

(* ****** ****** *)

(* end of [ats_filename.dats] *)
