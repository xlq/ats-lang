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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#
#include "libc/CATS/unistd.cats"
%} // end of [%{#]

(* ****** ****** *)

staload TYPES = "libc/sys/SATS/types.sats"

typedef off_t = $TYPES.off_t
typedef pid_t = $TYPES.pid_t
typedef uid_t = $TYPES.uid_t

typedef whence_t = $TYPES.whence_t

(* ****** ****** *)

staload FCNTL = "libc/SATS/fcntl.sats"
stadef fildes_v = $FCNTL.fildes_v

(* ****** ****** *)

sta STDIN_FILENO : int
sta STDOUT_FILENO : int
sta STDERR_FILENO : int
//
praxi STDIN_FILENO_gtez (): [STDIN_FILENO >= 0] void
praxi STDOUT_FILENO_gtez (): [STDOUT_FILENO >= 0] void
praxi STDERR_FILENO_gtez (): [STDERR_FILENO >= 0] void
//
macdef STDIN_FILENO = $extval (int STDIN_FILENO, "STDIN_FILENO")
macdef STDOUT_FILENO = $extval (int STDOUT_FILENO, "STDOUT_FILENO")
macdef STDERR_FILENO = $extval (int STDERR_FILENO, "STDERR_FILENO")

(* ****** ****** *)
//
// HX: implemented in [$ATSHOME/prelude/CATS/basics.cats]
//
fun stdin_fildes_view_get
  (): (fildes_v (STDIN_FILENO) | void)
  = "atspre_stdin_view_get"

fun stdin_fildes_view_set
  (pf: fildes_v (STDIN_FILENO) | (*none*)): void
  = "atspre_stdin_view_set"

//

fun stdout_fildes_view_get
  (): (fildes_v (STDOUT_FILENO) | void)
  = "atspre_stdout_view_get"

fun stdout_fildes_view_set
  (pf: fildes_v (STDOUT_FILENO) | (*none*)): void
  = "atspre_stdout_view_set"

//

fun stderr_fildes_view_get
  (): (fildes_v (STDERR_FILENO) | void)
  = "atspre_stderr_view_get"

fun stderr_fildes_view_set
  (pf: fildes_v (STDERR_FILENO) | (*none*)): void
  = "atspre_stderr_view_set"

(* ****** ****** *)
//
// implemented in [$ATSHOME/libc/DATS/unistd.dats]
//
fun fork_exn (): pid_t = "atslib_fork_exn"
  
fun fork_exec_cloptr_exn {v:view}
 (pf: !v | f: (v | (*none*)) -<cloptr1> void): void
 = "atslib_fork_exec_cloptr_exn"

fun fork_exec_and_wait_cloptr_exn (proc: () -<cloptr1> void): Int
  = "atslib_fork_exec_and_wait_cloptr_exn"

(* ****** ****** *)

dataview getcwd_v (m:int, l:addr, addr) =
  | {l>null} {n:nat} getcwd_v_succ (m, l, l) of strbuf_v (m, n, l)
  | getcwd_v_fail (m, l, null) of b0ytes (m) @ l
// end of [getcwd_v]

fun getcwd {m:nat} {l:addr}
  (pf: !b0ytes (m) @ l >> getcwd_v (m, l, l1) | p: ptr l, m: size_t m)
  : #[l1:addr] ptr l1 = "#atslib_getcwd"
// end of [getcwd]

(* ****** ****** *)
//
// HX: implemented in [$ATSHOME/libc/DATS/unistd.dats]
//
fun getcwd0 (): strptr1 = "atslib_getcwd0"
//
// HX:
// [get_current_dir_name] is available if _GNU_SOURCE is on
//
(* ****** ****** *)

symintr wait
fun wait_with_status {l:addr}
  (pf: !int? @ l >> int @ l | p: ptr l): pid_t = "atslib_wait_with_status"
overload wait with wait_with_status
fun wait_without_status (): pid_t = "atslib_wait_without_status"
overload wait with wait_without_status

(* ****** ****** *)

// [sleep] may be implemented using SIGARM
fun sleep {i:nat}
  (t: int i): [j:nat | j <= i] int j = "#atslib_sleep"
// end of [sleep]

(* ****** ****** *)

#define MILLION 1000000
// some systems require that the argument of usleep <= 1 million
fun usleep
  (n: natLte MILLION (* microseconds *)): void = "atslib_usleep" // !fun
// end of [usleep]

(* ****** ****** *)

fun getpagesize ():<> int = "#atslib_getpagesize" // macro

(* ****** ****** *)

fun getpid (): pid_t = "#atslib_getpid" // macro
fun getppid (): pid_t = "#atslib_getppid" // macro

(* ****** ****** *)

fun getuid ():<> uid_t = "#atslib_getuid" // macro
fun geteuid ():<> uid_t = "#atslib_geteuid" // macro

(* ****** ****** *)

// HX: non-reentrant version
fun getlogin ()
  :<!ref> [l:addr] (strptr l -<lin,prf> void | strptr l)
  = "#atslib_getlogin" // macro
// end of [getlogin]

dataview getlogin_v (m:int, l:addr, int) =
  | {n:nat} getlogin_v_succ (m, l, 0) of strbuf_v (m, n, l)
  | {i:int | i <> 0} getlogin_v_fail (m, l, i) of b0ytes (m) @ l
fun getlogin_r {m:int} {l:addr}
  (pf: !b0ytes (m) @ l >> getlogin_v (m, l, i) | p: ptr l, n: size_t)
  : #[i:int] int i // 0/!0: succ/fail
// end of [getlogin_r]

(* ****** ****** *)

fun chdir (path: string): int(*err*) = "#atslib_chdir"
fun fchdir {fd:int}
  (pf: !fildes_v (fd) | fd: int): int(*err*) = "#atslib_fchdir"
// end of [fchdir]

(* ****** ****** *)

fun link (src: string, dst: string): int = "#atslib_link"
fun unlink (path: string): int = "#atslib_unlink" // macro

(* ****** ****** *)

fun lseek_err {fd:int}
  (pf: !fildes_v (fd) | fd: int fd, ofs: off_t, whence: whence_t): off_t
  = "atslib_fildes_lseek_err"

fun lseek_exn {fd:int}
  (pf: !fildes_v (fd) | fd: int fd, ofs: off_t, whence: whence_t): off_t
  = "atslib_fildes_lseek_exn"

(* ****** ****** *)

fun fildes_pread
  {fd:int} {n,sz:nat | n <= sz} (
    pf: !fildes_v (fd)
  | fd: int fd, buf: &bytes sz, ntotal: size_t n, ofs: off_t
  ) : ssizeBtw(~1, n+1)
  = "atslib_fildes_pread"

fun fildes_pwrite
  {fd:int} {n,sz:nat | n <= sz} (
    pf: !fildes_v (fd)
  | fd: int fd, buf: &bytes sz, ntotal: size_t n, ofs: off_t
  ) : ssizeBtw(~1, n+1)
  = "atslib_fildes_pwrite"

(* ****** ****** *)

fun sync (): void = "#atslib_sync"

// [fsync] returns 0 on success or -1 on error
fun fsync {fd:int} // (sets errno)
  (pf: !fildes_v (fd) | fd: int fd): int = "#atslib_fsync"
// end of [fsync]

// [fdatasync] returns 0 on success or -1 on error
fun fdatasync {fd:int} // (sets errno)
  (pf: !fildes_v (fd) | fd: int fd): int = "#atslib_fdatasync"
// end of [fdatasync]

(* ****** ****** *)

abst@ype pathconfname_t = int
macdef _PC_LINK_MAX = $extval (pathconfname_t, "_PC_LINK_MAX")
macdef _PC_MAX_CANON = $extval (pathconfname_t, "_PC_MAX_CANON")
macdef _PC_MAX_INPUT = $extval (pathconfname_t, "_PC_MAX_INPUT")
macdef _PC_NAME_MAX = $extval (pathconfname_t, "_PC_NAME_MAX")
macdef _PC_PATH_MAX = $extval (pathconfname_t, "_PC_PATH_MAX")
macdef _PC_PIPE_BUF = $extval (pathconfname_t, "_PC_PIPE_BUF")
macdef _PC_CHOWN_RESTRICTED = $extval (pathconfname_t, "_PC_CHOWN_RESTRICTED")
macdef _PC_NO_TRUNC = $extval (pathconfname_t, "_PC_NO_TRUNC")
macdef _PC_VDISABLE = $extval (pathconfname_t, "_PC_VDISABLE")
macdef _PC_SYNC_IO = $extval (pathconfname_t, "_PC_SYNC_IO")
macdef _PC_ASYNC_IO = $extval (pathconfname_t, "_PC_ASYNC_IO")
macdef _PC_PRIO_IO = $extval (pathconfname_t, "_PC_PRIO_IO")
macdef _PC_SOCK_MAXBUF = $extval (pathconfname_t, "_PC_SOCK_MAXBUF")
macdef _PC_FILESIZEBITS = $extval (pathconfname_t, "_PC_FILESIZEBITS")
macdef _PC_REC_INCR_XFER_SIZE = $extval (pathconfname_t, "_PC_REC_INCR_XFER_SIZE")
macdef _PC_REC_MAX_XFER_SIZE = $extval (pathconfname_t, "_PC_REC_MAX_XFER_SIZE")
macdef _PC_REC_MIN_XFER_SIZE = $extval (pathconfname_t, "_PC_REC_MIN_XFER_SIZE")
macdef _PC_REC_XFER_ALIGN = $extval (pathconfname_t, "_PC_REC_XFER_ALIGN")
macdef _PC_ALLOC_SIZE_MIN = $extval (pathconfname_t, "_PC_ALLOC_SIZE_MIN")
macdef _PC_SYMLINK_MAX = $extval (pathconfname_t, "_PC_SYMLINK_MAX")
macdef _PC_2_SYMLINK = $extval (pathconfname_t, "_PC_2_SYMLINK")

fun pathconf
  (path: string, name: pathconfname_t): lint = "#atslib_pathconf"
// end of [pathconf]

//
// HX-2010-09-21: for simplicity, [fd] assumed to be valid
//
fun fpathconf {fd:nat}
  (fd: int fd, name: pathconfname_t): lint = "#atslib_fpathconf"
// end of [fpathconf]

(* ****** ****** *)

fun readlink {n:nat} {l:addr} (
  pf: !b0ytes(n) @ l >> bytes(n) @ l | path: string, p: ptr l, n: size_t n
) : [n1:int | n1 <= n] ssize_t (n1) = "#atslib_readlink"
// end of [readlink]

(* ****** ****** *)

fun setsid (): pid_t = "#atslib_setsid" // -1 is returned on error
fun getsid (pid: pid_t): pid_t = "#atslib_getsid" // -1 is returned on error

fun setpgid (
  pid: pid_t, pgid: pid_t
) : int = "#atslib_setpgid" // 0/-1 : succ/fail
fun getpgid (pid: pid_t): pid_t = "#atslib_getpgid" // -1 is returned on error

(* ****** ****** *)

fun tcsetpgrp {fd:nat}
  (fd: int fd, pgid: pid_t): int = "#atslib_tcsetpgrp" // 0/-1 : succ/fail
// end of [tcsetpgrp]
fun tcgetpgrp {fd:nat}
  (fd: int fd): pid_t = "#atslib_tcgetpgrp" // -1 is returned on error
// end of [tcgetpgrp]

(* ****** ****** *)

fun ttyname {fd:nat} (fd: int fd)
  :<!ref> [l:addr] (strptr l -<lin,prf> void | strptr l)
  = "#atslib_ttyname"
// end of [ttyname]

dataview
ttyname_v (m:int, l:addr, int) =
  | {n:nat | m > n}
    ttyname_v_succ (m, l, 0) of strbuf_v (m, n, l)
  | {i:int | i < 0} ttyname_v_fail (m, l, i) of b0ytes m @ l
fun ttyname_r
  {fd:nat} {m:nat} {l:addr} (
    pf: b0ytes m @ l
  | fd: int fd, p: ptr l, m: size_t m
  ) :<> [i:int | i <= 0] (ttyname_v (m, l, i) | int i)
  = "#atslib_ttyname_r" // if it fails, errno is returned
// end of [ttyname_r]

(* ****** ****** *)

fun isatty {fd:nat}
  (fd: int fd): int = "#atslib_isatty" // 1/0 : yes/no
// end of [isatty]

(* ****** ****** *)

(* end of [unistd.sats] *)
