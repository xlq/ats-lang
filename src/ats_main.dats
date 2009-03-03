(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS/Anairiats - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
 * Free Software Foundation; either version 3, or (at  your  option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *)

(* ****** ****** *)

// Time: July 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

%{^

#include "libc/CATS/stdio.cats"
#include "libc/CATS/stdlib.cats"

#include "ats_main.cats"

%}

(* ****** ****** *)

extern fun fopen_exn {m:file_mode}
  (s: string, m: file_mode m): [l:addr] (FILE m @ l | ptr l)
  = "atslib_fopen_exn"

extern fun fclose_exn {m:file_mode} {l:addr}
  (pf: FILE m @ l | p: ptr l):<!exnref> void = "atslib_fclose_exn"

// staload "libc/SATS/stdlib.sats"

extern fun getenv_opt (s: string):<!ref> Stropt = "atslib_getenv_opt"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

dynload "libats_lex_lexing.dats"

(* ****** ****** *)

dynload "ats_array.dats"
dynload "ats_charlst.dats"
dynload "ats_counter.dats"
dynload "ats_comarg.dats"
dynload "ats_debug.dats"
dynload "ats_effect.dats"
dynload "ats_error.dats"
dynload "ats_filename.dats"
dynload "ats_fixity.dats"
dynload "ats_global.dats"
dynload "ats_hashtbl.dats"
dynload "ats_intinf.dats"
dynload "ats_keyword.dats"
dynload "ats_label.dats"
dynload "ats_lexer_lats.dats"
dynload "ats_list.dats"
dynload "ats_location.dats"
dynload "ats_map_lin.dats"
dynload "ats_namespace.dats"
dynload "ats_posmark.dats"
dynload "ats_stamp.dats"
dynload "ats_set_fun.dats"
dynload "ats_symbol.dats"
dynload "ats_symenv.dats"
dynload "ats_symtbl.dats"
dynload "ats_syntax.dats"
dynload "ats_syntax_posmark.dats"

dynload "ats_parser.dats"

dynload "ats_staexp1.dats"
dynload "ats_staexp1_print.dats"
dynload "ats_dynexp1.dats"
dynload "ats_dynexp1_print.dats"
dynload "ats_trans1_env.dats"
dynload "ats_e1xp_eval.dats"
dynload "ats_trans1_sta.dats"
dynload "ats_trans1_dyn.dats"

dynload "ats_staexp2.dats"
dynload "ats_staexp2_print.dats"
dynload "ats_staexp2_scst.dats"
dynload "ats_staexp2_svVar.dats"
dynload "ats_staexp2_dcon.dats"
dynload "ats_staexp2_util1.dats"
dynload "ats_staexp2_util2.dats"
dynload "ats_dynexp2.dats"
dynload "ats_dynexp2_print.dats"
dynload "ats_dynexp2_dcst.dats"
dynload "ats_dynexp2_dmac.dats"
dynload "ats_dynexp2_dvar.dats"
dynload "ats_dynexp2_util.dats"
dynload "ats_trans2_env.dats"
dynload "ats_stadyncst2.dats"
dynload "ats_trans2_sta.dats"
dynload "ats_trans2_dyn.dats"
dynload "ats_macro2.dats"
dynload "ats_patcst2.dats"
dynload "ats_string_parse.dats"
dynload "ats_printf_c_lats.dats"
dynload "ats_staexp2_solve.dats"
dynload "ats_trans3_env_eff.dats"
dynload "ats_trans3_env_loop.dats"
dynload "ats_trans3_env_met.dats"
dynload "ats_trans3_env_scst.dats"
dynload "ats_trans3_env_state.dats"
dynload "ats_trans3_env.dats"
dynload "ats_trans3_env_print.dats"
dynload "ats_dynexp3.dats"
dynload "ats_dynexp3_print.dats"
dynload "ats_trans3_pat.dats"
dynload "ats_trans3_assgn.dats"
dynload "ats_trans3_deref.dats"
dynload "ats_trans3_view.dats"
dynload "ats_trans3_exp_up.dats"
dynload "ats_trans3_exp_dn.dats"
dynload "ats_trans3_loop.dats"
dynload "ats_trans3_dec.dats"

dynload "ats_solver_fm.dats"
dynload "ats_constraint.dats"
dynload "ats_constraint_print.dats"

dynload "ats_hiexp.dats"
dynload "ats_hiexp_print.dats"
dynload "ats_hiexp_util.dats"

dynload "ats_trans4.dats"

dynload "ats_ccomp.dats"
dynload "ats_ccomp_env.dats"
dynload "ats_ccomp_print.dats"
dynload "ats_ccomp_util.dats"
dynload "ats_ccomp_trans.dats"
dynload "ats_ccomp_trans_clau.dats"
dynload "ats_ccomp_trans_tailcal.dats"
dynload "ats_ccomp_trans_temp.dats"
dynload "ats_ccomp_emit.dats"
dynload "ats_ccomp_main.dats"

(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Fil = "ats_filename.sats"
staload Glo = "ats_global.sats"
staload Par = "ats_parser.sats"
staload PM = "ats_posmark.sats"

(* ****** ****** *)

staload "ats_comarg.sats"

staload Syn = "ats_syntax.sats"
staload DEXP1 = "ats_dynexp1.sats"
staload DEXP2 = "ats_dynexp2.sats"
staload DEXP3 = "ats_dynexp3.sats"
staload TransEnv1 = "ats_trans1_env.sats"
staload Trans1 = "ats_trans1.sats"
staload TransEnv2 = "ats_trans2_env.sats"
staload Trans2 = "ats_trans2.sats"
staload TransEnv3 = "ats_trans3_env.sats"
staload Trans3 = "ats_trans3.sats"
staload CSTR = "ats_constraint.sats"
staload Trans4 = "ats_trans4.sats"
staload CC = "ats_ccomp.sats"

(* ****** ****** *)

fn getenv_exn (name: string): String = let
  val stropt = getenv_opt name
in
  if stropt_is_some stropt then
    string1_of_string (stropt_unsome stropt)
  else begin
    prerr "The environment variable [";
    prerr name;
    prerr "] is undefined!\n" ;
    exit (1)
  end // end of [if]
end // end of [getenv_exn]

// this is primarily for ATS developers
fn atsopt_usage (cmd: string): void = begin
  printf ("usage: %s <command> ... <command>\n\n", @(cmd));
  print "where a <command> is of one of the following forms:\n\n";
  print "  -s filenames (for statically loading (many) <filenames>)\n";
  print "  --static filenames (for statically loading (many) <filenames>)\n";
  print "  -d filenames (for dynamically loading (many) <filenames>)\n";
  print "  --dynamic filenames (for dynamically loading (many) <filenames>)\n";
  print "  -o filename (output into <filename>)\n";
  print "  --output filename (output into <filename>)\n";
  print "  -dep (for generating dependency lists)\n";
  print "  --depgen (for generating dependency lists)\n";
  print "  -tc (for typechecking only)\n";
  print "  --typecheck (for typechecking only)\n";
  print "  --posmark_html_only (for generating a html file depicting colored concrete syntax)\n";
  print "  --debug=0 (for disabling the generation of debugging information)\n";
  print "  --debug=1 (for enabling the generation of debugging information)\n";
  print "  -h (for printing out the usage)\n";
  print "  --help (for printing out the usage)\n";
  print "  -v (for printing out the version)\n";
  print "  --version (for printing out the version)\n";
  print_newline ()
end // end of [atsopt_usage]

fn atsopt_version (): void = begin
  print "ATS/Anairiats version 0.1.1"; print_newline ()
end // end of [atsopt_version]

(* ****** ****** *)

// load in built-in fixity declarations
fn fixity_load (ATSHOME: string): void = let
  val basename = "prelude/fixity.ats"
  val fullname = $Fil.filename_append (ATSHOME, basename)
  val filename = $Fil.filename_make_absolute fullname
  val () = $Fil.the_filenamelst_push filename
  val d0cs = $Par.parse_from_filename (0 (*static*), filename)
  val () = $Fil.the_filenamelst_pop ()
  val d1cs = $Trans1.d0eclst_tr d0cs
  val () = $TransEnv1.the_fxtyenv_pervasive_add_topenv ()
(*
  val () = begin
    print "[fixity_load] is finished."; print_newline ()
  end
*)
in
  // empty
end // end of [fixity_load]

fn pervasive_load
  (ATSHOME: string, basename: string): void = let
  val fullname = $Fil.filename_append (ATSHOME, basename)
  val filename = $Fil.filename_make_absolute fullname
  val () = $Fil.the_filenamelst_push filename
(*
  val () = begin
    print "pervasive_load: parse: fullname = "; print fullname; print_newline ()
  end // end of [val]
*)
  val d0cs = $Par.parse_from_filename (0(*static*), filename)
(*
  val () = begin
    print "pervasive_load: parse: after: fullname = "; print fullname; print_newline ()
  end
*)
  val () = $Fil.the_filenamelst_pop ()
  val d1cs = $Trans1.d0eclst_tr d0cs
  val _(*d2cs*) = $Trans2.d1eclst_tr d1cs
in
  // empty
end // end of [pervasive_load]

fn prelude_load (ATSHOME: string): void = let
  val () = fixity_load (ATSHOME)
  val () = pervasive_load (ATSHOME, "prelude/basics_sta.sats")
(*
  val () = begin
    print "pervasive_load: loading [prelude/basics_sta.sats] is done.";
    print_newline ()
  end
*)
  val () = pervasive_load (ATSHOME, "prelude/sortdef.sats")
  val () = pervasive_load (ATSHOME, "prelude/basics_dyn.sats")
  val () = pervasive_load (ATSHOME, "prelude/macrodef.sats")
  //  [trans2_env_pervasive_add_topenv] needs to be called for the rest
  val () = $TransEnv2.trans2_env_pervasive_add_topenv ()

  // these are all the .sats files in $ATSHOME/prelude
  val () = pervasive_load (ATSHOME, "prelude/SATS/arith.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/bool.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/byte.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/char.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/file.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/float.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/integer.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/integer_ptr.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/lazy.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/lazy_vt.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/memory.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/pointer.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/printf.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/reference.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/sizetype.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/string.sats")

  // these are here because they are so commonly needed
  val () = pervasive_load (ATSHOME, "prelude/SATS/array.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/array0.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/list.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/list0.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/list_vt.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/matrix.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/option.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/slseg.sats")

(*
  val () = pervasive_load (ATSHOME, "prelude/SATS/slseg.sats")
*)

  val () = $TransEnv2.trans2_env_pervasive_add_topenv ()
  val () = $TransEnv3.trans3_env_initialize ()
in
  // empty
end // end of [prelude_load]

(* ****** ****** *)

datatype comkind =
  | COMKINDnone
  | COMKINDinput of int (* 0: static; 1: dynamic; 2: dynamic and main *)
  | COMKINDoutput

fn comkind_is_input (knd: comkind): bool =
  case+ knd of COMKINDinput _ => true | _ => false

fn comkind_is_output (knd: comkind): bool =
  case+ knd of COMKINDoutput _ => true | _ => false

(* ****** ****** *)

viewtypedef arglst (n:int) = list_vt (comarg, n)

(* ****** ****** *)

typedef param_t = @{
  comkind= comkind
, wait= int
, prelude= int
, posmark= int
, posmark_html= int
, posmark_only= int
, typecheck_only= int
} // end of [param_t]

(* ****** ****** *)

local

typedef fil_t = $Fil.filename_t
val the_input_filename = ref_make_elt<fil_t> ($Fil.filename_stdin)

in // in of [local]

fn input_filename_get (): fil_t = !the_input_filename
fn input_filename_set (fil: fil_t) = (!the_input_filename := fil)

end // end of [local]

(* ****** ****** *)

fn do_parse_filename
  (flag: int, param: param_t, basename: string)
  : $Syn.d0eclst = let
  val debug_flag = $Deb.debug_flag_get ()
  val () = if debug_flag > 0 then let
    val cwd = getcwd () where {
      // staload "libc/SATS/unistd.sats"
      extern fun getcwd (): String = "atslib_getcwd"
    }
  in
    prerr "cwd = "; prerr cwd; prerr_newline ()
  end // end of [if]

  val filename = (
    case+ $Fil.filenameopt_make basename of
    | ~Some_vt filename => filename
    | ~None_vt () => begin
        prerr "error: the filename ["; prerr basename;
        prerr "] is not available."; prerr_newline ();
        exit (1)
      end
  ) : $Fil.filename_t
  val () = input_filename_set (filename)
  val depgen = $Glo.ats_depgenflag_get ()
  val () = begin
    if depgen > 0 then (print_string basename; print_string ":")
  end
  var d0cs: $Syn.d0eclst = list_nil ()
  val () = if param.posmark > 0 then let
    val (pf_posmark | ()) = $PM.posmark_initiate ()
    val () = $Fil.the_filenamelst_push filename
    val () = d0cs := $Par.parse_from_filename (flag, filename)
    val () = $Fil.the_filenamelst_pop ()
    val () = $Syn.d0eclst_posmark d0cs
    val () = begin
      if param.posmark_html > 0 then $PM.posmark_file_make_htm (basename)
    end
    val () = $PM.posmark_terminate (pf_posmark | (*none*))
    val () = begin
      print "The phase of syntax marking of [";
      print basename; print "] is successfully completed!";
      print_newline ()
    end // end of [val]
  in
    // empty
  end else let
    val () = $Fil.the_filenamelst_push filename
    val () = d0cs := $Par.parse_from_filename (flag, filename)
    val () = $Fil.the_filenamelst_pop ()
  in
    // empty
  end // end of [if param.posmark > 0]

  val () = if depgen > 0 then print_newline ()
in
  d0cs // the return value
end // end of [do_parse_filename]

(* ****** ****** *)

fn do_parse_stdin
  (flag: int, param: param_t)
  : $Syn.d0eclst = let
  (* no support for position marking *)
  val () = $Fil.the_filenamelst_push $Fil.filename_stdin
  val d0cs = $Par.parse_from_stdin (flag)
  val () = $Fil.the_filenamelst_pop ()
in
  d0cs
end // end of [do_parse_stdin]

(* ****** ****** *)

local

val the_output_filename = ref_make_elt<Stropt> (stropt_none)

in // in of [local]

fn output_filename_get (): Stropt = !the_output_filename
fn output_filename_set (name: Stropt) = (!the_output_filename := name)

end // end of [local]

(* ****** ****** *)

fn do_trans12
  (basename: string, d0cs: $Syn.d0eclst): $DEXP2.d2eclst = let
  val debug_flag = $Deb.debug_flag_get ()

  val () = $Trans1.initialize ()
  val d1cs = $Trans1.d0eclst_tr d0cs
  val () = $Trans1.finalize ()
  val () = if debug_flag > 0 then begin
    prerr "The 1st translation (fixity) of [";
    prerr basename;
    prerr "] is successfully completed!";
    prerr_newline ()
  end // end of [if]

  val d2cs = $Trans2.d1eclst_tr d1cs
  val () = if debug_flag > 0 then begin
    prerr "The 2nd translation (binding) of [";
    prerr basename;
    prerr "] is successfully completed!";
    prerr_newline ()
  end // end of [if]
in
  d2cs
end // end of [do_trans12]

fn do_trans123
  (basename: string, d0cs: $Syn.d0eclst): $DEXP3.d3eclst = let
  val d2cs = do_trans12 (basename, d0cs)
  val d3cs = $Trans3.d2eclst_tr d2cs
  val c3t = $Trans3.c3str_final_get ()
  val () = $CSTR.c3str_solve (c3t)
  val debug_flag = $Deb.debug_flag_get ()
  val () = if debug_flag > 0 then begin
    prerr "The 3rd translation (typechecking) of [";
    prerr basename;
    prerr "] is successfully completed!";
    prerr_newline ()
  end // end of [if]
in
  d3cs
end // end of [do_trans123]

fn do_trans1234
  (flag: int, basename: string, d0cs: $Syn.d0eclst): void = let
  val d3cs = do_trans123 (basename, d0cs)
  val hids = $Trans4.d3eclst_tr (d3cs)
  val debug_flag = $Deb.debug_flag_get ()
  val () = if debug_flag > 0 then begin
    prerr "The 4th translation (proof erasure) of [";
    prerr basename;
    prerr "] is successfully completed!";
    prerr_newline ()
  end // end of [if]
  val infil = input_filename_get ()
  val outname = output_filename_get ()
in
  case+ outname of
  | _ when stropt_is_some (outname) => let
      prval pf_mod = file_mode_lte_w_w
      val outname = stropt_unsome (outname)
      val file_mode_w = $extval (file_mode w, "\"w\"")
      val (pf_out | p_out) = fopen_exn (outname, file_mode_w)
      val () = $CC.ccomp_main (pf_mod | flag, !p_out, infil, hids)
      val () = fprintf1_exn (
        pf_mod
      | !p_out
      , "\n/* ****** ****** */\n\n/* end of [%s] */\n"
      , @(outname)
      ) // end of [fprintf]
      val () = if debug_flag > 0 then begin
        prerr "The 5th translation (code emission) of [";
        prerr basename;
        prerr "] is successfully completed!";
        prerr_newline ()
      end // end of [if]
    in
      fclose_exn (pf_out | p_out)
    end // end of [_ when ...]
  | _ => let
    prval pf_mod = file_mode_lte_w_w
    val (pf_stdout | p_stdout) = stdout_get ()
    val () = $CC.ccomp_main
      (pf_mod | flag, !p_stdout, infil, hids)
    val () = fprint1_string
      (pf_mod | !p_stdout, "\n/* ****** ****** */\n")
  in
    stdout_view_set (pf_stdout | (*none*))
  end // end of [_]
end // end of [do_trans1234]

(* ****** ****** *)

%{^

#if _ATS_BOOTSTRAP

ats_void_type mainats_prelude () { return ; }

#endif

%}

(* ****** ****** *)

extern fun IATS_wait_set (): void = "ats_main_IATS_wait_set"
extern fun IATS_wait_is_set (): bool = "ats_main_IATS_wait_is_set"
extern fun IATS_wait_clear (): void = "ats_main_IATS_wait_clear"

extern fun is_IATS_flag (s: string): bool = "ats_main_is_IATS_flag"
extern fun IATS_extract (s: string): Stropt = "ats_main_IATS_extract"

(* ****** ****** *)

implement main {n} (argc, argv) = let
val () = gc_chunk_count_limit_max_set (~1) // [~1]: infinite

(*
val () = gc_chunk_count_limit_max_set (0) // for testing GC heavily
*)

val () = ATSHOMERELOC_set () where {
  extern fun ATSHOMERELOC_set (): void = "ats_main_ATSHOMERELOC_set"
}

val ATSHOME = ATSHOME_getenv_exn () where {
  extern fun ATSHOME_getenv_exn (): string = "ats_main_ATSHOME_getenv_exn"
}

val () = $Fil.the_prepathlst_push ATSHOME // for the run-time and lib
val () = $TransEnv2.trans2_env_initialize ()

fn warning (str: string) = begin
  prerr "Waring: unrecognized command line argument [";
  prerr str; prerr "] is ignored."; prerr_newline ()
end // end of [warning]

fun loop {i:nat | i <= n} .<i>. (
    argv: &(@[string][n]), param: &param_t, args: arglst i
  ) :<cloptr1> void = begin case+ args of
  | ~list_vt_cons (arg, args) => begin case+ arg of
    | _ when IATS_wait_is_set () => let
        val COMARGkey (_(*n*), dir) = arg
        val () = IATS_wait_clear (); val () = $Fil.the_pathlst_push dir
      in
        loop (argv, param, args)
      end // end of [_ when ...]
(*
    | _ when ATSHOME_RELOC_wait_is_set () => let
        val COMARGkey (_(*n*), dir) = arg
        val () = ATSHOME_RELOC_wait_clear (); val () = atshome_reloc_dir_set (dir)
      in
        loop (argv, param, args)
      end // end of [_ when ...]
*)
    | COMARGkey (1, str) => let
        val () = param.comkind := COMKINDnone (); val () =
          case+ str of
          | "-s" => begin
              param.comkind := COMKINDinput 0; param.wait := 1
            end // end of ["-s"]
          | "-d" => begin
              param.comkind := COMKINDinput 1; param.wait := 1
            end // end of ["-d"]
          | "-o" => begin
              param.comkind := COMKINDoutput ()
            end
          | "-dep" => $Glo.ats_depgenflag_set (1)
          | "-tc" => (param.typecheck_only := 1)
          | "-h" => begin
              param.comkind := COMKINDnone (); atsopt_usage (argv.[0])
            end // end of ["-h"]
          | "-v" => atsopt_version ()
          | _ when is_IATS_flag str => let
              val dir = IATS_extract str
            in
              if stropt_is_some dir then begin
                $Fil.the_pathlst_push (stropt_unsome dir)
              end else begin
                IATS_wait_set ()
              end // end of [if]
            end // end of [_ when ...]
          | _ => ()
      in
        loop (argv, param, args)
      end // end of [COMARGkey (1, _)]
    | COMARGkey (2, str) => let
        val () = param.comkind := COMKINDnone (); val () =
          case+ str of
          | "--static" => begin
              param.comkind := COMKINDinput 0; param.wait := 1
            end // end of ["--static"]
          | "--dynamic" => begin
              param.comkind := COMKINDinput 1; param.wait := 1
            end // end of ["--dynamic"]
          | "--output" => begin
              param.comkind := COMKINDoutput ()
            end // end of ["--output"]
          | "--depgen" => $Glo.ats_depgenflag_set (1)
          | "--typecheck" => (param.typecheck_only := 1)
          | "--posmark_html" => begin
              param.posmark := 1; param.posmark_html := 1
            end // end of ["--posmark_html"]
          | "--posmark_html_only" => begin
              param.posmark := 1; param.posmark_html := 1; param.posmark_only := 1
            end // end of ["--posmark_html_only"]
          | "--debug=0" => $Deb.debug_flag_set (0)
          | "--debug=1" => $Deb.debug_flag_set (1)
          | "--help" => begin
              param.comkind := COMKINDnone (); atsopt_usage (argv.[0])
            end // end of ["--help"]
          | "--version" => atsopt_version ()
          | _ => warning (str)
      in
        loop (argv, param, args)
      end // end of [COMARG (2, _)]
    | _ when comkind_is_input (param.comkind) => let
        var flag: int = 0; val () = begin
          case+ param.comkind of COMKINDinput i => flag := i | _ => ()
        end // end of [val]
        val COMARGkey (_(*n*), name) = arg; val () = param.wait := 0
        val () = begin // loading prelude if needed
          if param.prelude = 0 then (param.prelude := 1; prelude_load ATSHOME)
        end
        val d0cs = do_parse_filename (flag, param, name)
        val () = begin case+ 0 of
          | _ when param.posmark_only > 0 => ()
          | _ when $Glo.ats_depgenflag_get () > 0 => ()
          | _ when param.typecheck_only > 0 => let
              val _(*d3cs*) = do_trans123 (name, d0cs)
            in
              prerrf ("The file [%s] is successfully typechecked!", @(name));
              prerr_newline ()
            end // end of [_ when ...]
          | _ => do_trans1234 (flag, name, d0cs)
        end // end of [val]
      in
        loop (argv, param, args)
      end // end of [_ when ...]
    | _ when comkind_is_output (param.comkind) => let
        val () = param.comkind := COMKINDnone ()
        val COMARGkey (_(*n*), name) = arg
        val name = string1_of_string name
        val () = output_filename_set (stropt_some name)
      in
        loop (argv, param, args)
      end // end of [_ when ...]
    | COMARGkey (_, str) => let
        val () = param.comkind := COMKINDnone ()
      in
        warning (str); loop (argv, param, args)
      end // end of [_]
    end // end of [list_vt_cons]
  | ~list_vt_nil () when param.wait > 0 => begin
    case+ param.comkind of
    | COMKINDinput flag => let
        val () =
          if param.prelude = 0 then begin
            param.prelude := 1; prelude_load (ATSHOME)
          end
        val d0cs = do_parse_stdin (flag, param)
        val () = begin case+ 0 of
          | _ when param.posmark_only > 0 => ()
          | _ when $Glo.ats_depgenflag_get () > 0 => ()
          | _ when param.typecheck_only > 0 => let
              val _(*d3cs*) = do_trans123 ("stdin", d0cs)
            in
              prerr ("The typechecking is successfully completed!");
              prerr_newline ()
            end
          | _ => do_trans1234 (flag, "stdin", d0cs)
        end
      in
        // empty
      end // end of [COMKINDinput]
    | _ => ()
    end // end of [list_vt_nil whne param.wait > 0]
  | ~list_vt_nil () => ()
end // end of [loop]

val+ ~list_vt_cons (_, args) = comarglst_parse (argc, argv)
var param: param_t = @{
  comkind= COMKINDnone ()
, wait= 0
, prelude= 0
, posmark= 0
, posmark_html= 0
, posmark_only= 0
, typecheck_only= 0
}

val () = loop (argv, param, args)

in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [ats_main.dats] *)
