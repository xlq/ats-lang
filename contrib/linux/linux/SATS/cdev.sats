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
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
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
#include "linux/cdev.cats"
%} // end of [%{#]

(* ****** ****** *)

staload
FS = "linux/SATS/fs.sats"
viewtypedef inode = $FS.inode

staload
TYPES = "linux/SATS/types.sats"
typedef dev_t = $TYPES.dev_t

(* ****** ****** *)

viewtypedef
cdev_struct =
  $extype_struct "cdev_struct" of {
  dev= dev_t
, count= uint
} // end of [cdev_struct]
viewtypedef cdev = cdev_struct

absviewtype cdev_ref (l:addr, sd: int)

(* ****** ****** *)

fun cdev_alloc // HX: dynamically allocated cdev
  () : [l:agez] cdev_ref (l, 1) = "#atsctrb_linux_cdev_alloc"
// end of [cdev_alloc]

(* ****** ****** *)

fun cdev_init {l:agz}
  (pf: cdev? @ l | p: ptr l, fops: ptr): cdev_ref (l, 0)
  = "atsctrb_linux_cdev_init" // end of [cdev_init]

(* ****** ****** *)

fun cdev_put {l:agz} {sd:int}
  (dev: cdev_ref (l, sd)): void = "atsctrb_linux_cdev_put"
// end of [cdev_put]

(* ****** ****** *)

fun cdev_add {l:agz} {sd:int} (
  dev: !cdev_ref (l, sd), num: dev_t, count: uint
) : #[i:int | i <= 0] int (i) = "atsctrb_linux_cdev_add"

fun cdev_del {l:addr} {sd:int}
  (dev: !cdev_ref (l, sd) >> ptr l): (option_v (cdev? @ l, sd==0) | void)
  = "#atsctrb_linux_cdev_del" // end of [cdev_del]

(* ****** ****** *)

fun cdev_index
  (inode: &inode): int = "atsctrb_linux_cdev_index"
// end of [cdev_index]

fun cd_forget (inode: &inode): int = "atsctrb_linux_cd_forget"

(* ****** ****** *)

(* end of [cdev.sats] *)


////


#ifndef _LINUX_CDEV_H
#define _LINUX_CDEV_H

#include <linux/kobject.h>
#include <linux/kdev_t.h>
#include <linux/list.h>

struct file_operations;
struct inode;
struct module;

struct cdev {
	struct kobject kobj;
	struct module *owner;
	const struct file_operations *ops;
	struct list_head list;
	dev_t dev;
	unsigned int count;
};

void cdev_init(struct cdev *, const struct file_operations *);

struct cdev *cdev_alloc(void);

void cdev_put(struct cdev *p);

int cdev_add(struct cdev *, dev_t, unsigned);

void cdev_del(struct cdev *);

int cdev_index(struct inode *inode);

void cd_forget(struct inode *);

extern struct backing_dev_info directly_mappable_cdev_bdi;

#endif
