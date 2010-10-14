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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#include "prelude/params.hats"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then
#print "Loading [arith.sats] starts!\n"
#endif // end of [VERBOSE_PRELUDE]

(* ****** ****** *)

dataprop MUL (int, int, int) =
  | {n:int} MULbas (0, n, 0)
  | {m,n,p:int | m >= 0} MULind (m+1, n, p+n) of MUL (m, n, p)
  | {m,n,p:int | m > 0} MULneg (~m, n, ~p) of MUL (m, n, p)
// end of [MUL]

(* ****** ****** *)

praxi mul_make : {m,n:int} () -<prf> MUL (m, n, m*n)
praxi mul_elim : {m,n:int} {p:int} MUL (m, n, p) -<prf> [p == m*n] void

//
// HX: (m+i)*n = m*n+i*n
//
praxi mul_add_const {i:int}
  {m,n:int} {p:int} (pf: MUL (m, n, p)):<prf> MUL (m+i, n, p+i*n)
// end of [mul_add_const]

//
// HX: (ax+b)*(cy+d) = ac*xy + ad*x + bc*y + bd
//
praxi mul_expand_linear
  {a,b:int} {c,d:int} // a,b,c,d: constants!
  {x,y:int} {xy:int} (pf: MUL (x, y, xy)):<prf> MUL (a*x+b, c*y+d, a*c*xy+a*d*x+b*c*y+b*d)
// end of [mul_expand_linear]

//
// HX: (a1x1+a2x2+b)*(c1y1+c2y2+d) = ...
//
praxi mul_expand2_linear // a1,b1,c1,a2,b2,c2: constants!
  {a1,a2,b:int} {c1,c2,d:int}
  {x1,x2:int} {y1,y2:int} {x1y1,x1y2,x2y1,x2y2:int} (
    pf11: MUL (x1, y1, x1y1), pf12: MUL (x1, y2, x1y2)
  , pf21: MUL (x2, y1, x2y1), pf22: MUL (x2, y2, x2y2)
  ) :<prf> MUL (
      a1*x1+a2*x2+b
    , c1*y1+c2*y2+d
    , a1*c1*x1y1
    + a1*c2*x1y2
    + a2*c1*x2y1
    + a2*c2*x2y2
    + a1*d*x1 + a2*d*x2
    + b*c1*y1 + b*c2*y2
    + b*d
    ) // end of [MUL]
// end of [mul_expand2_linear]

(* ****** ****** *)

prfun mul_istot {m,n:int} ():<prf> [p:int] MUL (m, n, p)

prfun mul_isfun {m,n:int} {p1,p2:int}
  (pf1: MUL (m, n, p1), pf2: MUL (m, n, p2)):<prf> [p1==p2] void

(* ****** ****** *)

prfun mul_nat_nat_nat :
  {m,n:nat} {p:int} MUL (m, n, p) -<prf> [p >= 0] void

(* ****** ****** *)

prfun mul_negate {m,n:int} {p:int} (pf: MUL (m, n, p)):<prf> MUL (~m, n, ~p)

(* ****** ****** *)

prfun mul_commute {m,n:int} {p:int} (pf: MUL (m, n, p)):<prf> MUL (n, m, p)

(* ****** ****** *)
//
// HX: m*(n1+n2) = m*n1+m*n2
//
prfun mul_distribute {m,n1,n2:int} {p1,p2:int}
  (pf1: MUL (m, n1, p1), pf2: MUL (m, n2, p2)):<prf> MUL (m, n1+n2, p1+p2)
//
// HX: (m1+m2)*n = m1*n + m2*n
//
prfun mul_distribute2 {m1,m2,n:int} {p1,p2:int}
  (pf1: MUL (m1, n, p1), pf2: MUL (m2, n, p2)):<prf> MUL (m1+m2, n, p1+p2)

(* ****** ****** *)

prfun mul_associate {x,y,z:int} {xy,yz,xy_z,x_yz:int} (
    pf1: MUL (x, y, xy)
  , pf2: MUL (y, z, yz)
  , pf3: MUL (xy, z, xy_z)
  , pf4: MUL (x, yz, x_yz)
  ) :<prf> [xy_z==x_yz] void

(* ****** ****** *)

dataprop GCD (int, int, int) =
  | {m:nat} GCDbas1 (m, 0, m)
  | {n:pos} GCDbas2 (0, n, n)
  | {m:pos;n:int | m <= n} {r:int} GCDind1 (m, n, r) of GCD (m, n-m, r)
  | {m:int;n:pos | m > n } {r:int} GCDind2 (m, n, r) of GCD (m-n, n, r)
  | {m:nat;n:int | n < 0} {r:int} GCDneg1 (m, n, r) of GCD (m, ~n, r)
  | {m:int;n:int | m < 0} {r:int} GCDneg2 (m, n, r) of GCD (~m, n, r)
// end of [GCD]

prfun gcd_is_fun {m,n:int} {r1,r2:int}
  (pf1: GCD (m, n, r1), pf2: GCD (m, n, r2)):<prf> [r1==r2] void

prfun gcd_modulo {m,n:int} {r:int}
  (pf: GCD (m, n, r)):<prf> [s1,s2:int] (MUL (s1, r, m), MUL (s2, r, n))

prfun gcd_commute {m,n:int} {r:int} (pf: GCD (m, n, r)):<prf> GCD (n, m, r)

(* ****** ****** *)

dataprop EXP2 (int, int) =
  | {n:nat} {p:nat} EXP2ind (n+1, 2*p) of EXP2 (n, p)
  | EXP2bas (0, 1)
// end of [EXP2]

// proven in [arith.dats]
prfun EXP2_istot {n:nat} (): [p:nat] EXP2 (n, p)
prfun EXP2_isfun {n:nat} {p1,p2:int}
  (pf1: EXP2 (n, p1), pf2: EXP2 (n, p2)): [p1==p2] void
// end of [EXP2_isfun]

// proven in [arith.dats]
prfun EXP2_monotone {n1,n2:nat | n1 <= n2} {p1,p2:int}
  (pf1: EXP2 (n1, p1), pf2: EXP2 (n2, p2)): [p1 <= p2] void

// proven in [arith.dats]
prfun EXP2_mul {n1,n2:nat | n1 <= n2} {p1,p2:nat} {p:int}
  (pf1: EXP2 (n1, p1), pf2: EXP2 (n2, p2), pf3: MUL (p1, p2, p))
  : EXP2 (n1+n2, p)

(* ****** ****** *)

#if VERBOSE_PRELUDE #then
#print "Loading [arith.sats] finishes!\n"
#endif // end of [VERBOSE_PRELUDE]

(* end of [arith.sats] *)
