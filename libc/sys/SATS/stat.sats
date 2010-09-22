(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Power of Types!
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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)  *)

(* ****** ****** *)

staload T = "libc/sys/SATS/types.sats"
typedef dev_t = $T.dev_t
typedef ino_t = $T.ino_t
typedef mode_t = $T.mode_t
typedef nlink_t = $T.nlink_t
//
typedef gid_t = $T.gid_t
typedef uid_t = $T.uid_t
//
typedef off_t = $T.off_t
//
typedef blkcnt_t = $T.blkcnt_t
typedef blksize_t = $T.blksize_t
//
typedef time_t = $T.time_t

(* ****** ****** *)

%{#
#include "libc/sys/CATS/stat.cats"
%} // end of [%{#]

(* ****** ****** *)

abst@ype stat_t_rest // unknown quantity
typedef stat_t =
$extype_struct "ats_stat_type" of {
  st_dev= dev_t // device
, st_ino= ino_t // 32-bit file serial number
, st_mode= mode_t // file mode
, st_nlink= nlink_t // link count
, st_uid= uid_t // user ID of the file's owner
, st_gid= gid_t // group ID of the file's group
, st_rdev= dev_t // device number if device
, st_size= off_t // size of file in bytes
, st_blksize= blksize_t // optimal block size for I/O
, st_blocks= blkcnt_t // number 512-byte blocks allocated
, st_atime= time_t // time of last access
, st_mtime= time_t // time of last modification
, st_ctime= time_t // time of last status change
, _rest= stat_t_rest // this abstract field cannot be accessed
} // end of [stat_t]

(* ****** ****** *)

//
// HX: bit masks and values
//
macdef S_IFMT = $extval (mode_t, "S_IFMT")
macdef S_IFBLK = $extval (mode_t, "S_IFBLK")
macdef S_IFCHR = $extval (mode_t, "S_IFCHR")
macdef S_IFDIR = $extval (mode_t, "S_IFDIR")
macdef S_IFIFO = $extval (mode_t, "S_IFIFO")
macdef S_IFLNK = $extval (mode_t, "S_IFLNK")
macdef S_IFREG = $extval (mode_t, "S_IFREG")
macdef S_IFSOCK = $extval (mode_t, "S_IFSOCK")

(* ****** ****** *)

macdef S_IRWXU = $extval (mode_t, "S_IRWXU")
macdef S_IRUSR = $extval (mode_t, "S_IRUSR")
macdef S_IWUSR = $extval (mode_t, "S_IWUSR")
macdef S_IXUSR = $extval (mode_t, "S_IXUSR")

macdef S_IRWXG = $extval (mode_t, "S_IRWXG")
macdef S_IRGRP = $extval (mode_t, "S_IRGRP")
macdef S_IWGRP = $extval (mode_t, "S_IWGRP")
macdef S_IXGRP = $extval (mode_t, "S_IXGRP")

macdef S_IRWXO = $extval (mode_t, "S_IRWXO")
macdef S_IROTH = $extval (mode_t, "S_IROTH")
macdef S_IWOTH = $extval (mode_t, "S_IWOTH")
macdef S_IXOTH = $extval (mode_t, "S_IXOTH")

macdef S_ISUID = $extval (mode_t, "S_ISUID")
macdef S_ISGID = $extval (mode_t, "S_ISGID")
macdef S_ISVTX = $extval (mode_t, "S_ISVTX")

(* ****** ****** *)
//
// HX: macros
//
fun S_ISBLK (m: mode_t): bool = "atslib_S_ISBLK"
fun S_ISCHR (m: mode_t): bool = "atslib_S_ISCHR"
fun S_ISDIR (m: mode_t): bool = "atslib_S_ISDIR"
fun S_ISFIFO (m: mode_t): bool = "atslib_S_ISFIFO"
fun S_ISREG (m: mode_t): bool = "atslib_S_ISREG"
fun S_ISLNK (m: mode_t): bool = "atslib_S_ISLNK"
fun S_ISSOCK (m: mode_t): bool = "atslib_S_ISSOCK"

(* ****** ****** *)

fun chmod_err (path: string, mode: mode_t): int
  = "atslib_chmod_err"
fun chmod_exn (path: string, mode: mode_t): void
  = "atslib_chmod_exn"

(* ****** ****** *)

fun mkdir_err (path: string, mode: mode_t): int
  = "atslib_mkdir_err"
fun mkdir_exn (path: string, mode: mode_t): void
  = "atslib_mkdir_exn"

(* ****** ****** *)

fun stat_err {l:addr} (
    name: string, st: &stat_t? >> opt (stat_t, i==0)
  ) : #[i:int | i <= 0] int i
  = "atslib_stat_err"
fun stat_exn (name: string, st: &stat_t? >> stat_t): void
  = "atslib_stat_exn"

fun lstat_err {l:addr} (
    name: string, st: &stat_t? >> opt (stat_t, i==0)
  ) : #[i:int | i <= 0] int i
  = "atslib_lstat_err"
fun lstat_exn (name: string, buf: &stat_t? >> stat_t): void
  = "atslib_lstat_exn"

(* ****** ****** *)

fun umask (mask_new: mode_t): mode_t(*mask_old*) = "atslib_umask"

(* ****** ****** *)

(* end of [stat.sats] *)
