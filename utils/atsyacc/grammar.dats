(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2009 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
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
 *
 *)

(* ****** ****** *)

// February 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "top.sats"

(* ****** ****** *)

local

assume rule_t (n:int) = '{
  rule_num= int
, rule_lhs= symbol_t
, rule_rhs= array (symbol_t, n), rule_nrhs= int n
, rule_act = string (* code *)
} // end of [rule]

val the_rule_count = ref_make_elt<int> (0)

in // in of [local]

implement rule_make {n} (lhs, rhs, nrhs, act) = let
  val n = !the_rule_count; val () = !the_rule_count := n+1
in '{
  rule_num= n
, rule_lhs= lhs, rule_rhs= rhs, rule_nrhs= nrhs
, rule_act= act
} end // end of [rule_make]

end // end of [local]

(* ****** ****** *)

(* end of [grammar.dats] *)
