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
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
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

// author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

// some built-in dynamic constants

#include "prelude/params.hats"

#if VERBOSE_PRELUDE #then

#print "Loading [basics_dyn.sats] starts!\n"

#endif

(* ****** ****** *)

// some overloaded symbols

symintr ~ not
symintr && || << >> land lor lxor
symintr + - * / mod gcd
symintr < <= > >= = <>
symintr succ pred
symintr abs square sqrt cube cbrt
symintr compare max min pow
symintr foreach // foreach without index
symintr iforeach (* foreach with index *)
symintr fprint print prerr
symintr length (* array_length, list_length, string_length, etc. *)
symintr ofstring tostring

symintr liftmac evalmac

symintr assert assert_errmsg

symintr int_of uint_of
symintr int1_of uint1_of
symintr lint_of ulint_of
symintr llint_of ullint_of
symintr sint_of usint_of
symintr ssint_of ussint_of
symintr float_of double_of ldouble_of

(* ****** ****** *)

//
// should this be assumed?
// praxi eqsize_byte_one (): [sizeof byte == 1] void
//

praxi eqsize_byte_char (): [sizeof byte == sizeof char] void
praxi eqsize_int_uint (): [sizeof int == sizeof uint] void
praxi eqsize_char_schar (): [sizeof char == sizeof schar] void
praxi eqsize_char_uchar (): [sizeof char == sizeof uchar] void

(* ****** ****** *)

(*
**
** The proof function [verify_constraint] is mostly used for
** debugging proofs, and it is equivalent to the follow line:
**
** prval _ = (): [p] void
**
** Note that the followine line puts [p] into the assumption
** store after verification is done:
**
** prval () = (): [p] void 
**
*)

prfun verify_constraint {p:bool | p} (): void 

(* ****** ****** *)

(*
val AssertionException : exn = "AssertionException"
val DivisionByZeroException : exn = "DivisionByZeroException"
val OverflowException : exn = "OverflowException"
val SubscriptException : exn = "SubscriptException"
*)

(* ****** ****** *)

val{elt:viewt@ype} sizeof : size_t (sizeof elt)
val{elt:viewt@ype} junkof : elt?

(* ****** ****** *)

// note that sizeof(empty) = 0 and sizeof(void) = 1
val empval : empty = "ats_empty_value" // the empty value in ATS

val true : bool (true) and false : bool (false)

fun exit {a:viewt@ype} (status: int):<!exn> a
  = "ats_exit"
// end of [exit]

fun exit_main {a:viewt@ype}
  {v_in:view} {v_out:view}
  (pf: !v_in >> v_out | status: int):<!exn> a
  = "ats_exit"
// end of [exit_main]

fun exit_errmsg {a:viewt@ype}
  (status: int, msg: string):<!exnref> a
  = "ats_exit_errmsg"
// end of [exit_errmsg]

fun exit_prerrf {a:viewt@ype} {ts:types}
  (status: int, fmt: printf_c ts, args: ts):<!exnref> a
  = "atspre_exit_prerrf"
// end of [exit_prerrf]

(* ****** ****** *)

fun assert_bool (assertion: bool):<!exn> void
  = "atspre_assert"
overload assert with assert_bool

fun assert_bool1 {b:bool} (assertion: bool b):<!exn> [b] void
  = "atspre_assert"
overload assert with assert_bool1

//

fun assert_errmsg_bool
  (assertion: bool, msg: string):<!exnref> void
  = "atspre_assert_errmsg"
overload assert_errmsg with assert_errmsg_bool

fun assert_errmsg_bool1 {b:bool}
  (assertion: bool b, msg: string):<!exnref> [b] void
  = "atspre_assert_errmsg"
overload assert_errmsg with assert_errmsg_bool1

//

fun assert_errmsg_bool_string1
  (assertion: bool, msg: String):<!exnref> void
  = "atspre_assert_errmsg"
overload assert_errmsg with assert_errmsg_bool_string1

fun assert_errmsg_bool1_string1 {b:bool}
  (assertion: bool b, msg: String):<!exnref> [b] void
  = "atspre_assert_errmsg"
overload assert_errmsg with assert_errmsg_bool1_string1

(* ****** ****** *)

//
// If [main_dummy] is implemented, then it indicates that [mainats]
// is implemented in C
//

prval main_dummy (): void

(* ****** ****** *)

//
// for internal use: [main_prelude] is called before [main]
// it is implemented in "$ATSHOME/ats_main_prelude.dats"
//

fun main_prelude (): void = "mainats_prelude"

(* ****** ****** *)

(*

fun main {n:int | n >= 1} (argc: int n, argv: &(@[string][n])): void
  = "mainats"

*)

symintr main

fun main_void (): void = "mainats"
fun main_argc_argv
  {n:int | n >= 1} (argc: int n, argv: &(@[string][n])): void
  = "mainats"

overload main with main_void
overload main with main_argc_argv

(* ****** ****** *)

symintr free_gc_elim

praxi free_gc_addr_elim // return the certificate to the GC
  {l:addr} (pf: free_gc_v l):<> void

praxi free_gc_t0ype_addr_elim // return the certificate to the GC
  {a:viewt@ype} {l:addr} (pf: free_gc_v (a, l)):<> void

praxi free_gc_t0ype_int_addr_elim // return the certificate to the GC
  {a:viewt@ype} {n:int} {l:addr} (pf: free_gc_v (a, n, l)):<> void

overload free_gc_elim with free_gc_addr_elim
overload free_gc_elim with free_gc_t0ype_addr_elim
overload free_gc_elim with free_gc_t0ype_int_addr_elim

(* ****** ****** *)

// implemented in [basics.cats]

castfn cloptr_get_view_ptr {a:viewt@ype}
  (x: cloptr a):<> [l:addr] (free_gc_v l, clo a @ l | ptr l)
  = "atspre_cloptr_get_view_ptr"

castfn cloptr_make_view_ptr {a:viewt@ype} {l:addr}
  (pf_gc: free_gc_v l, pf_at: clo a @ l | p: ptr l):<> cloptr a
  = "atspre_cloptr_make_view_ptr"

castfn cloref_get_view_ptr {a:t@ype}
  (x: cloref a):<> [l:addr] (vbox (clo a @ l) | ptr l)
  = "atspre_cloref_get_view_ptr"

castfn cloref_make_view_ptr {a:t@ype}
  {l:addr} (pf: vbox (clo a @ l) | p: ptr l):<> cloref a
  = "atspre_cloref_make_view_ptr"
  
fun cloptr_free {a:t@ype} (x: cloptr a):<> void
  = "atspre_cloptr_free"

(* ****** ****** *)

// implemented in [basic.cats]

castfn objmod_upcast
  {c1,c2:cls | c1 <= c2} (x: objmod c1):<> objmod c2
  = "atspre_objmod_upcast"

(* ****** ****** *)

// fun void ():<> void = "ats_void"

// [vbox_make_view_ptr] implemented in [basics.cats]
fun vbox_make_view_ptr
  {a:viewt@ype} {l:addr} // for statically allocated
  (_: a @ l | _: ptr l):<> (vbox (a @ l) | void)
  = "atspre_vbox_make_view_ptr"

(* ****** ****** *)

praxi opt_some {a:viewt@ype} (x: !(a) >> opt (a, true)):<prf> void
praxi opt_unsome {a:viewt@ype} (x: !opt (a, true) >> a):<prf> void

praxi opt_none {a:viewt@ype} (x: !(a?) >> opt (a, false)):<prf> void
praxi opt_unnone {a:viewt@ype} (x: !opt (a, false) >> a?):<prf> void

(* ****** ****** *)

(*

// fractional views are yet to be supported

sta zero : rat and one : rat

prval vfrac_make : {v:view} v -<> [s:stamp] vfrac (s, v, one)
  and vfrac_free : {v:view} {s:stamp} vfrac (s, v, one) -<> v
  and vfrac_split : {v:view} {r:rat} {s:stamp}
    vfrac (s, v, r) -<> (vfrac (s, v, r/2), vfrac (s, v, r/2))
  and vfrac_unsplit : {v:view} {r1,r2: rat} {s:stamp}
    (vfrac (s, v, r1), vfrac (s, v, r2)) -<> vfrac (s, v, r1+r2)

fun vtfrac_make {vt:viewtype} (_: vt):<> [s:stamp] vtfrac (s, vt, one)
and vtfrac_free {vt:viewtype} {s:stamp} (_: vtfrac (s, vt, one)):<> vt
and vtfrac_split {vt:viewtype} {r:rat} {s:stamp}
  (_: vtfrac (s, vt, r)):<> (vtfrac (s, vt, r/2), vtfrac (s, vt, r/2))
and vtfrac_unsplit {vt:viewtype} {r1,r2:rat} {s:stamp}
  (_: vtfrac (s, vt, r1), vtfrac (s, vt, r2)):<> vtfrac (s, vt, r1+r2)

*)

(* ****** ****** *)

abstype file_mode (file_mode) // string type

dataprop file_mode_lte (file_mode, file_mode) =
  | {m:file_mode} file_mode_lte_refl (m, m)
  | {m1,m2,m3:file_mode}
      file_mode_lte_tran (m1, m3) of
        (file_mode_lte (m1, m2), file_mode_lte (m2, m3))
  | {m:file_mode} file_mode_lte_rw_r (rw, r)
  | {m:file_mode} file_mode_lte_rw_w (rw, w)

prval file_mode_lte_r_r: file_mode_lte (r, r) // implemented in [file.dats]
prval file_mode_lte_w_w: file_mode_lte (w, w) // implemented in [file.dats]
prval file_mode_lte_rw_rw: file_mode_lte (rw, rw) // implemented in [file.dats]

stadef <= = file_mode_lte

(* ****** ****** *)

(* standard I/O channels *)

// standard input

sta stdin_addr : addr
macdef stdin = $extval (ptr stdin_addr, "stdin")

fun stdin_get ():<!exnref> (FILE r @ stdin_addr | ptr stdin_addr)
  = "atspre_stdin_get"
fun stdin_view_get ():<!exnref> (FILE r @ stdin_addr | void)
  = "atspre_stdin_view_get"
and stdin_view_set (pf: FILE r @ stdin_addr | (*none*)):<!exnref> void
  = "atspre_stdin_view_set"

fun stdin_view_get_opt ()
  :<!ref> [b:bool] (option_v (FILE r @ stdin_addr, b) | bool b)
  = "atspre_stdin_view_get_opt"
and stdin_view_set_opt (pf: FILE r @ stdin_addr | (*none*))
  :<!ref> [b:bool] (option_v (FILE r @ stdin_addr, ~b) | bool b)
  = "atspre_stdin_view_set_opt"

// standard output

sta stdout_addr : addr

macdef stdout = $extval (ptr stdout_addr, "stdout")

fun stdout_get ()
  :<!exnref> (FILE w @ stdout_addr | ptr stdout_addr)
  = "atspre_stdout_get"
fun stdout_view_get ()
  :<!exnref> (FILE w @ stdout_addr | void)
  = "atspre_stdout_view_get"
and stdout_view_set
  (pf: FILE w @ stdout_addr | (*none*)):<!exnref> void
  = "atspre_stdout_view_set"

fun stdout_view_get_opt ()
  :<!ref> [b:bool] (option_v (FILE w @ stdout_addr, b) | bool b)
  = "atspre_stdout_view_get_opt"
and stdout_view_set_opt (pf: FILE w @ stdout_addr | (*none*))
  :<!ref> [b:bool] (option_v (FILE w @ stdout_addr, ~b) | bool b)
  = "atspre_stdout_view_set_opt"

// standard error

sta stderr_addr : addr

macdef stderr = $extval (ptr stderr_addr, "stderr")

fun stderr_get ()
  :<!exnref> (FILE w @ stderr_addr | ptr stderr_addr)
  = "atspre_stderr_get"

fun stderr_view_get ()
  :<!exnref> (FILE w @ stderr_addr | void)
  = "atspre_stderr_view_get"

and stderr_view_set
  (pf: FILE w @ stderr_addr | (*none*)):<!exnref> void
  = "atspre_stderr_view_set"

fun stderr_view_get_opt ()
  :<!ref> [b:bool] (option_v (FILE w @ stderr_addr, b) | bool b)
  = "atspre_stderr_view_get_opt"

and stderr_view_set_opt
  (pf: FILE w @ stderr_addr | (*none*))
  :<!ref> [b:bool] (option_v (FILE w @ stderr_addr, ~b) | bool b)
  = "atspre_stderr_view_set_opt"

(* ****** ****** *)

// print functions for various type of data

typedef
fprint_t0ype_type (a:t@ype) = {m:file_mode}
  (file_mode_lte (m, w) | &FILE m, a) -<fun,!exnref> void

typedef
fprint_viewt0ype_type (a:viewt@ype) = {m:file_mode}
  (file_mode_lte (m, w) | &FILE m, !a) -<fun,!exnref> void

// print functions for newlines

symintr fprint_newline

fun fprint0_newline (out: FILEref):<!ref> void
  = "atspre_fprint_newline"

fun fprint1_newline {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m):<!ref> void
  = "atspre_fprint_newline"

overload fprint_newline with fprint0_newline
overload fprint_newline with fprint1_newline

(* ****** ****** *)

fun print_newline ():<!ref> void
  = "atspre_print_newline"

and prerr_newline ():<!ref> void
  = "atspre_prerr_newline"

(* ****** ****** *)

// implemented in libats/basics.dats
prval option_v_unsome : {v:view} option_v (v, true) -<prf> v
prval option_v_unnone : {v:view} option_v (v, false) -<prf> void

// implemented in stdlib/basics.dats
prval unit_v_elim : unit_v -<prf> void

(* ****** ****** *)

(*

// it is now supported internally; see [lazy.cats]

// for lazy call-by-need evaluation

// nonlinear version
dataviewtype thunkvalue (a:t@ype+) =
  | thunkvalue_thunk (a) of (() -<cloref1,~ref> a)
  | thunkvalue_value (a) of a
// end of [thunkvalue]

// linear version
dataviewtype thunkvalue_vt (a:viewt@ype+) =
  | thunkvalue_vt_thunk (a) of (() -<lin,cloptr1,~ref> a)
  | thunkvalue_vt_value (a) of a
// end of [thunkvalue_vt]

// implemented in [prelude/DATS/lazy.dats]
fun{a:t@ype} lazy_force_crypt (x: crypt (lazy a)):<1,~ref> a
macdef lazy_force (x) = lazy_force_crypt ($encrypt ,(x))

// implemented in [prelude/DATS/lazy.dats]
fun{a:viewt@ype} lazy_vt_force_crypt (x: crypt (lazy_vt a)):<1,~ref> a
macdef lazy_vt_force (x) = lazy_vt_force_crypt ($encrypt ,(x))

*)

fun lazy_vt_free {a:viewt@ype} (x: lazy_vt a):<1,~ref> void
  = "ats_lazy_vt_free"

overload ~ with lazy_vt_free

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [basics_dyn.ats] finishes!\n"

#endif

(* end of [basics_dyn.sats] *)
