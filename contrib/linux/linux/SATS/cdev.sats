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
stadef inode = $FS.inode

staload
MOD = "linux/SATS/module.sats"
stadef module_ref = $MOD.module_ref
stadef module_ref1 = $MOD.module_ref1

staload
TYPES = "linux/SATS/types.sats"
stadef dev_t = $TYPES.dev_t

(* ****** ****** *)

abstype file_operations_ptr = ptr

(* ****** ****** *)

(*
struct cdev {
	struct kobject kobj;
	struct module *owner;
	const struct file_operations *ops;
	struct list_head list;
	dev_t dev;
	unsigned int count;
} ; // end of [struct cdev]
*)

viewtypedef
cdev_struct =
  $extype_struct "cdev_struct" of {
  empty= empty
, module= module_ref1
, ops= file_operations_ptr
, dev= dev_t
, count= uint
, _rest= undefined
} // end of [cdev_struct]
viewtypedef cdev = cdev_struct

(* ****** ****** *)
//
// HX-2011-02-10:
// this type is ref-counted
//
absviewtype cdev_ref (l:addr, sd: int) // sd: static(0)/dynamic(1)
//
(* ****** ****** *)

fun cdev_get_owner
  {l:agz} {sd:int} (dev: cdev_ref (l, sd)): [l1: agz] (
  minus (cdev_ref (l, sd), module_ref (l1)) | module_ref (l1)
) // end of [cdev_get_owner]

(* ****** ****** *)
/*
struct cdev *cdev_alloc(void);
*/
fun cdev_alloc // HX: dynamically allocated cdev
  () : [l:agez] cdev_ref (l, 1) = "#atsctrb_linux_cdev_alloc"
// end of [cdev_alloc]

(* ****** ****** *)
/*
void cdev_init(struct cdev *, const struct file_operations *);
*/
fun cdev_init {l:agz} (
  pf: cdev? @ l | p: ptr l, fops: file_operations_ptr
) : cdev_ref (l, 0) = "atsctrb_linux_cdev_init"

(* ****** ****** *)
//
// HX-2011-02-10: ref-count decrement
//
/*
void cdev_put(struct cdev *p);
*/
fun cdev_put {l:agz} {sd:int}
  (dev: cdev_ref (l, sd)): void = "#atsctrb_linux_cdev_put"
// end of [cdev_put]

(* ****** ****** *)
/*
int cdev_add(struct cdev *, dev_t, unsigned);
*/
fun cdev_add {l:agz} {sd:int} (
  dev: !cdev_ref (l, sd), num: dev_t, count: uint
) : #[i:int | i <= 0] int (i) = "atsctrb_linux_cdev_add"

(* ****** ****** *)
/*
void cdev_del(struct cdev *);
*/
fun cdev_del {l:addr} {sd:int} (
  dev: !cdev_ref (l, sd) >> ptr l
) : (option_v (cdev? @ l, sd==0) | void) = "#atsctrb_linux_cdev_del"
// end of [cdev_del]

(* ****** ****** *)
/*
int cdev_index(struct inode *inode);
*/
fun cdev_index
  (inode: &inode): int = "atsctrb_linux_cdev_index"
// end of [cdev_index]

(* ****** ****** *)
/*
void cd_forget(struct inode *);
*/
fun cd_forget (inode: &inode): int = "#atsctrb_linux_cd_forget"

(* ****** ****** *)
/*
extern struct backing_dev_info directly_mappable_cdev_bdi;
*/

local

staload
BDI = "linux/SATS/backing-dev.sats"
stadef backing_dev_info = $BDI.backing_dev_info

in

fun directly_mappable_cdev_bdi_get (): [l:addr]
  (backing_dev_info @ l, backing_dev_info @ l -<lin,prf> void | ptr l)
// end of [directly_mappable_cdev_bdi_get]

end // end of [local]

(* ****** ****** *)

(* end of [cdev.sats] *)
