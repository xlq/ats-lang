(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-20?? Hongwei Xi, ATS Trustworthy Software, Inc.
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
//
// Author: Hongwei Xi (gmhwxi AT gmail DOT com)
// Start Time: August, 2011
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "libc/SATS/stdio.sats"

(* ****** ****** *)

staload "atsdoc_translate.sats"

(* ****** ****** *)
//
dynload "atsdoc_translate.dats"
dynload "atsdoc_translate_error.dats"
dynload "atsdoc_translate_item.dats"
//
(* ****** ****** *)
//
dynload "libatsdoc/dynloadall.dats" // HX: for libatsdoc.o
//
(* ****** ****** *)

datatype comarg = COMARGkey of (int, string)
viewtypedef comarglst (n: int) = list_vt (comarg, n)

(* ****** ****** *)

extern
fun comarg_parse (s: string):<> comarg
extern
fun comarglst_parse {n:nat}
  (argc: int n, argv: &(@[string][n])):<> list_vt (comarg, n)
// end of [comarglst_parse]

(* ****** ****** *)

implement
comarg_parse (s) = let
  fun loop {n,i:nat | i <= n} .<n-i>.
    (s: string n, n: int n, i: int i):<> comarg = 
    if i < n then begin
      if (s[i] <> '-') then COMARGkey (i, s) else loop (s, n, i+1)
    end else begin
      COMARGkey (n, s) (* loop exists *)
    end // end of [if]
  // end of [loop]
  val s = string1_of_string s
  val n = string_length s; val n = int1_of_size1 n
in
  loop (s, n, 0)
end // end of [comarg_parse]

implement
comarglst_parse
  {n} (argc, argv) = let
  viewtypedef arglst (n: int) = list_vt (comarg, n)
  fun loop {i:nat | i <= n} {l:addr} .<n-i>.
    (pf0: arglst 0 @ l | argv: &(@[string][n]), i: int i, p: ptr l)
    :<cloref> (arglst (n-i) @ l | void) =
    if i < argc then let
      val+ ~list_vt_nil () = !p
      val arg = comarg_parse (argv.[i])
      val lst0 = list_vt_cons (arg, list_vt_nil ())
      val+ list_vt_cons (_, !lst) = lst0
      val (pf | ()) = loop (view@ (!lst) | argv, i+1, lst)
    in
      fold@ lst0; !p := lst0; (pf0 | ())
    end else (pf0 | ())
  var lst0 = list_vt_nil {comarg} ()
  val (pf | ()) = loop (view@ lst0 | argv, 0, &lst0) // tail-call
  prval () = view@ lst0 := pf
in
  lst0
end // end of [comarglst_parse]

(* ****** ****** *)

fn comarg_warning
  (str: string) = {
  val () = prerr "waring(ATSDOC)"
  val () = prerr ": unrecognized command line argument ["
  val () = prerr str
  val () = prerr "] is ignored."
  val () = prerr_newline ()
} // end of [comarg_warning]

(* ****** ****** *)

datatype
waitkind =
  | WAITKINDnone of ()
  | WAITKINDinput of () // -i ...
  | WAITKINDtoutput of () // -co ... // code
  | WAITKINDdoutput of () // -do ... // data
// end of [waitkind]

typedef
cmdstate = @{
  comarg0= comarg
//
, waitkind= waitkind
//
, ninputfile= int // number of processed input files
//
} // end of [cmdstate]

(* ****** ****** *)

fn isinpwait
  (state: cmdstate): bool =
  case+ state.waitkind of
  | WAITKINDinput () => true | _ => false
// end of [isinpwait]

fn istoutwait
  (state: cmdstate): bool =
  case+ state.waitkind of
  | WAITKINDtoutput () => true | _ => false
// end of [istoutwait]

fn isdoutwait
  (state: cmdstate): bool =
  case+ state.waitkind of
  | WAITKINDdoutput () => true | _ => false
// end of [isdoutwait]

(* ****** ****** *)

local
//
typedef FILErefopt = Option (FILEref)
//
val theCout = ref<FILEref> (stdout_ref)
val theDout = ref<FILErefopt> (None ())

in // in of [local]

fun tout_get (): FILEref = !theCout
fun tout_set
  (x: FILEref) : void = let
  val () = fclose_exn (!theCout) in !theCout := x
end  // end of [tout_set]

fun dout_get (): FILErefopt = !theDout
fun dout_set (
  x: FILErefopt
) : void = let
  val () = (case+ !theDout of
    | Some fil => fclose_exn (fil) | None () => ()
  ) : void // end of [val]
in
  !theDout := x
end  // end of [dout_set]

end // end of [local]

fun tout_set_filename
  (path: string): void = let
  val (pfopt | filp) = fopen_err (path, file_mode_w)
in
  if filp > null then let
    prval Some_v (pffil) = pfopt
    val fil = __cast (pffil | filp) where {
      extern castfn __cast {m:fm} {l:addr} (pf: FILE (m) @ l | p: ptr l): FILEref 
    } // end of [val]
  in
    tout_set (fil)
  end else let
    prval None_v () = pfopt in (*nothing*)
  end // end of [if]
end // end of [tout_set_filename]

fun dout_set_filename
  (path: string): void = let
  val (pfopt | filp) = fopen_err (path, file_mode_w)
in
  if filp > null then let
    prval Some_v (pffil) = pfopt
    val fil = __cast (pffil | filp) where {
      extern castfn __cast {m:fm} {l:addr} (pf: FILE (m) @ l | p: ptr l): FILEref 
    } // end of [val]
  in
    dout_set (Some fil)
  end else let
    prval None_v () = pfopt in dout_set (None)
  end // end of [if]
end // end of [dout_set_filename]

(* ****** ****** *)

fn*
process_cmdline
  {i:nat} .<i,0>. (
  state: &cmdstate, arglst: comarglst (i)
) :<fun1> void = let
(*
  val () = prerrf ("process_cmdline: enter\n")
*)
in
//
case+ arglst of
| ~list_vt_cons (arg, arglst) => (
    process_cmdline2 (state, arg, arglst)
  ) // endof [list_vt_cons]
| ~list_vt_nil ()
    when state.ninputfile = 0 => let
    val tout = tout_get ()
    val () = trans_top_from_stdin (tout)
    val dout = dout_get ()
    val () = (case+ dout of
      | Some filr => fprint_the_tranitmlst (filr, "STDIN") | None () => ()
    ) : void // end of [val]
  in
    // nothing
  end // end of [list_vt_nil when ...]
| ~list_vt_nil () => ()
//
end // end of [process_cmdline]

and
process_cmdline2
  {i:nat} .<i,2>. (
  state: &cmdstate
, arg: comarg, arglst: comarglst (i)
) :<fun1> void = let
in
//
case+ arg of
| _ when isinpwait (state) => let
//
// HX: the [inpwait] state stays unchanged
//
    val nif = state.ninputfile
  in
    case+ arg of
    | COMARGkey (1, key) when nif > 0 =>
        process_cmdline2_COMARGkey1 (state, arglst, key)
    | COMARGkey (2, key) when nif > 0 =>
        process_cmdline2_COMARGkey2 (state, arglst, key)
    | COMARGkey (_, basename) => let
        val () = state.ninputfile := state.ninputfile + 1
        val tout = tout_get ()
        val () = trans_top_from_basename (tout, basename)
        val dout = dout_get ()
        val () = (case+ dout of
          | Some filr => fprint_the_tranitmlst (filr, basename) | None () => ()
        ) : void // end of [val]
      in
        process_cmdline (state, arglst)
      end (* end of [_] *)
  end // end of [_ when isinpwait]
| _ when istoutwait (state) => let
    val () = state.waitkind := WAITKINDnone ()
    val COMARGkey (_, basename) = arg
    val () = tout_set_filename (basename)
  in
    process_cmdline (state, arglst)
  end // end of [_ when istoutwait]
| _ when isdoutwait (state) => let
    val () = state.waitkind := WAITKINDnone ()
    val COMARGkey (_, basename) = arg
    val () = dout_set_filename (basename)
  in
    process_cmdline (state, arglst)
  end // end of [_ when isdoutwait]
| COMARGkey (1, key) =>
    process_cmdline2_COMARGkey1 (state, arglst, key)
| COMARGkey (2, key) =>
    process_cmdline2_COMARGkey2 (state, arglst, key)
| COMARGkey (_, key) => let
    val () = state.waitkind := WAITKINDnone ()
    val () = comarg_warning (key)
  in
    process_cmdline (state, arglst)
  end
//
end // end of [process_cmdline2]

and
process_cmdline2_COMARGkey1
  {i:nat} .<i,1>. (
  state: &cmdstate
, arglst: comarglst (i)
, key: string
) :<fun1> void = let
  val () = state.waitkind := WAITKINDnone ()
  val () = (case+ key of
    | "-i" => {
        val () = state.ninputfile := 0
        val () = state.waitkind := WAITKINDinput
      }
    | "-to" => {
        val () = state.waitkind := WAITKINDtoutput ()
      }
    | "-do" => {
        val () = state.waitkind := WAITKINDdoutput ()
      }
(*
    | "-v" => atsdoc_version (stdout_ref)
*)
    | _ => comarg_warning (key)
  ) : void // end of [val]
in
  process_cmdline (state, arglst)
end // end of [process_cmdline2_COMARGkey1]

and
process_cmdline2_COMARGkey2
  {i:nat} .<i,1>. (
  state: &cmdstate
, arglst: comarglst (i)
, key: string
) :<fun1> void = let
  val () = state.waitkind := WAITKINDnone ()
  val () = (case+ key of
    | "--input" => {
        val () = state.ninputfile := 0
        val () = state.waitkind := WAITKINDinput
      }
    | "--toutput" => {
        val () = state.waitkind := WAITKINDtoutput ()
      }
    | "--doutput" => {
        val () = state.waitkind := WAITKINDdoutput ()
      }
(*
    | "--version" => atsdoc_version (stdout_ref)
*)
    | _ => comarg_warning (key)
  ) : void // end of [val]
in
  process_cmdline (state, arglst)
end // end of [process_cmdline2_COMARGkey2]

(* ****** ****** *)

implement
main (
  argc, argv
) = () where {
(*
*)
//
val arglst = comarglst_parse (argc, argv)
val ~list_vt_cons (arg0, arglst) = arglst
//
var state = @{
  comarg0 = arg0
//
, waitkind= WAITKINDnone ()
//
, ninputfile= 0
//
} : cmdstate
//
val () = process_cmdline (state, arglst)
//
val tout = tout_get ()
val () = fclose_exn (tout)
val dout = dout_get ()
val () = (case+ dout of
  | Some fil => fclose_exn (fil) | None () => ()
) : void // end of [val]
//
} // end of [main]

(* ****** ****** *)

(* end of [atsdoc_main.dats] *)
