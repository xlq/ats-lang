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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#

#include "libc/sys/CATS/types.cats" // for [pid_t]
#include "libc/CATS/unistd.cats"

%}

(* ****** ****** *)

staload TYPES = "libc/sys/SATS/types.sats"

typedef off_t = $TYPES.off_t
typedef pid_t = $TYPES.pid_t
typedef uid_t = $TYPES.uid_t

typedef whence_t = $TYPES.whence_t

(* ****** ****** *)

staload FCNTL = "libc/SATS/fcntl.sats"

sortdef open_flag = $FCNTL.open_flag

stadef open_flag_lte = $FCNTL.open_flag_lte

stadef rd = $FCNTL.open_flag_rd
stadef wr = $FCNTL.open_flag_wr

stadef fildes_v = $FCNTL.fildes_v

(* ****** ****** *)

sta stdin_int : int
sta stdout_int : int
sta stderr_int : int

macdef STDIN_FILENO = $extval (int stdin_int, "STDIN_FILENO")
macdef STDOUT_FILENO = $extval (int stdout_int, "STDOUT_FILENO")
macdef STDERR_FILENO = $extval (int stderr_int, "STDERR_FILENO")

(* ****** ****** *)

// implemented in [$ATSHOME/prelude/CATS/basics.cats]

fun stdin_fildes_view_get (): (fildes_v (stdin_int, rd) | void)
  = "atspre_stdin_view_get"

fun stdin_fildes_view_set (pf: fildes_v (stdin_int, rd) | (*none*)): void
  = "atspre_stdin_view_set"

//

fun stdout_fildes_view_get (): (fildes_v (stdout_int, wr) | void)
  = "atspre_stdout_view_get"

fun stdout_fildes_view_set (pf: fildes_v (stdout_int, wr) | (*none*)): void
  = "atspre_stdout_view_set"

//

fun stderr_fildes_view_get (): (fildes_v (stderr_int, wr) | void)
  = "atspre_stderr_view_get"

fun stderr_fildes_view_set (pf: fildes_v (stderr_int, wr) | (*none*)): void
  = "atspre_stderr_view_set"

(* ****** ****** *)

// implemented in [$ATSHOME/libc/DATS/unistd.dats]

fun fork_exn (): pid_t = "atslib_fork_exn"
  
fun fork_exec_cloptr_exn {v:view}
 (pf: !v | f: (v | (*none*)) -<cloptr1> void): void
 = "atslib_fork_exec_cloptr_exn"

fun fork_exec_and_wait_cloptr_exn (proc: () -<cloptr1> void): Int
  = "atslib_fork_exec_and_wait_cloptr_exn"

(* ****** ****** *)

// implemented in [$ATSHOME/libc/DATS/unistd.dats]
fun getcwd (): String = "atslib_getcwd"

(* ****** ****** *)

symintr wait
fun wait_with_status {l:addr}
  (pf: !int? @ l >> int @ l | p: ptr l): pid_t
  = "atslib_wait_with_status"

and wait_without_status (): pid_t
  = "atslib_wait_without_status"

overload wait with wait_with_status
overload wait with wait_without_status

(* ****** ****** *)

// [sleep] may be implemented using SIGARM
fun sleep {i:nat} (t: int i): [j:nat | j <= i] int j
  = "atslib_sleep"

(* ****** ****** *)

#define MILLION 1000000
// some systems require that the argument of usleep <= 1 million
fun usleep (n: natLte MILLION (* microseconds *)): void
  = "atslib_usleep"

(* ****** ****** *)

fun getpagesize ():<> int = "#atslib_getpagesize" // macro

(* ****** ****** *)

fun getpid (): pid_t = "#atslib_getpid" // macro
fun getppid (): pid_t = "#atslib_getppid" // macro

(* ****** ****** *)

fun getuid ():<> uid_t = "#atslib_getuid" // macro
fun geteuid ():<> uid_t = "#atslib_geteuid" // macro

(* ****** ****** *)

fun chdir_err (path: string): int(*err*) = "#atslib_chdir_err"
fun chdir_exn (path: string): void = "atslib_chdir_exn" // function

fun fchdir_err {fd:int} {flag:open_flag}
  (pf: !fildes_v (fd, flag) | fd: int): int(*err*) = "#atslib_fchdir_err"
// end of [fchdir_err]

fun fchdir_exn {fd:int} {flag:open_flag}
  (pf: !fildes_v (fd, flag) | fd: int): void = "atslib_fchdir_exn" // fun
// end of [fchdir_exn]

(* ****** ****** *)

fun link_err
  (src: string, dst: string): int = "#atslib_link_err" // macro
// end of [link_err]
fun link_exn
  (src: string, dst: string): void = "atslib_link_exn" // function
// end of [link_exn]

fun unlink_err (path: string): int = "#atslib_unlink_err" // macro
fun unlink_exn (path: string): void = "atslib_unlink_exn" // function

(* ****** ****** *)

fun fildes_lseek_err {fd:int} {flag:open_flag}
  (pf: !fildes_v (fd, flag) | fd: int fd, ofs: off_t, whence: whence_t): off_t
  = "atslib_fildes_lseek_err"

fun fildes_lseek_exn {fd:int} {flag:open_flag}
  (pf: !fildes_v (fd, flag) | fd: int fd, ofs: off_t, whence: whence_t): off_t
  = "atslib_fildes_lseek_exn"

(* ****** ****** *)

fun fildes_pread_err
  {fd:int} {flag:open_flag} {n,sz:nat | n <= sz} (
    pf1: open_flag_lte (flag, rd), pf2: !fildes_v (fd, flag)
  | fd: int fd, buf: &bytes sz, ntotal: size_t n, ofs: off_t
  ) : ssizeBtw(~1, n+1)
  = "atslib_fildes_pread_err"

fun fildes_pwrite_err
  {fd:int} {flag:open_flag} {n,sz:nat | n <= sz} (
    pf1: open_flag_lte (flag, wr), pf2: !fildes_v (fd, flag)
  | fd: int fd, buf: &bytes sz, ntotal: size_t n, ofs: off_t
  ) : ssizeBtw(~1, n+1)
  = "atslib_fildes_pwrite_err"

(* ****** ****** *)

fun sync (): void = "atslib_sync"

// [fsync] returns 0 on success or -1 on error
fun fsync_err {fd:int} {flag:open_flag} // (sets errno)
  (pf: !fildes_v (fd, flag) | fd: int fd): int
  = "atslib_fsync"

// [fdatasync] returns 0 on success or -1 on error
fun fdatasync_err {fd:int} {flag:open_flag} // (sets errno)
  (pf: !fildes_v (fd, flag) | fd: int fd): int
  = "atslib_fdatasync"
  
(* ****** ****** *)

(* end of [unistd.sats] *)
