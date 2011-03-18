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
#include "contrib/linux/linux/CATS/fs.cats"
%} // end of [%{#]

(* ****** ****** *)

staload TYPES = "contrib/linux/linux/SATS/types.sats"
typedef dev_t = $TYPES.dev_t

(* ****** ****** *)

propdef ftakeout_p
  (v1:view, v2:view) = v1 -<prf> (v2, v2 -<lin,prf> v1)

(* ****** ****** *)

viewtypedef
inode =
$extype_struct "inode_struct" of {
  empty= empty
, i_state= ulint
, dirtied_when= ulint (* jiffies or first dirtying *)
, i_flags= uint
, _rest= undefined_vt
} // end of [inode]

(* ****** ****** *)

absview inode_v (l:addr)
prfun inode_v_takeout
  : {l:addr} ftakeout_p (inode_v l, inode @ l)
// end of [inode_v_takeout]

absviewtype inode_ref (l:addr) = ptr
viewtypedef inode_ref0 = [l:agez] inode_ref (l)
viewtypedef inode_ref1 = [l:addr | l > null] inode_ref (l)
//
prfun
inode_ref_unfold
  {l:agz} (
  x: !inode_ref (l) >> ptr l
) : (
  inode_v l | void
) // end of [inode_ref_unfold]
//
prfun
inode_ref_fold
  {l:addr} (
  pf: inode_v l | x: !ptr l >> inode_ref l
) : void // end of [inode_ref_fold]
//
castfn ptr_of_inode {l:addr} (x: inode_ref (l)):<> ptr (l)
overload ptr_of with ptr_of_inode
//
(* ****** ****** *)

viewtypedef
super_block =
$extype_struct "super_block_struct" of {
  empty= empty
, s_dev= dev_t
, s_blocksize= ulint
, s_blocksize_bits= uchar
, s_dirt= uchar
, s_maxbytes= ullint
, _rest= undefined_vt
} // end of [super_block]

(* ****** ****** *)

fun new_inode (
  sb: &super_block
) : inode_ref0 = "mac#atsctrb_linux_new_inode"
// end of [new_inode]

(* ****** ****** *)

(* end of [fs.sats] *)
