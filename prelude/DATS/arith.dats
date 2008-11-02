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
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

implement mul_isfun (pf1, pf2) = let
  prfun isfun {m:nat;n:int} {p1,p2:int} .<m>.
    (pf1: MUL (m, n, p1), pf2: MUL (m, n, p2)): [p1==p2] void =
    case+ (pf1, pf2) of
    | (MULbas (), MULbas ()) => ()
    | (MULind pf1, MULind pf2) => isfun (pf1, pf2)
  // end of [isfun]
in
  case+ (pf1, pf2) of
  | (MULneg pf1, MULneg pf2) => isfun (pf1, pf2)
  | (_, _) =>> isfun (pf1, pf2)
end // end of [mul_isfun]

implement mul_istot {m,n} () = let
  prfun istot {m:nat;n:int} .<m>. (): [p:int] MUL (m, n, p) =
    sif m > 0 then begin
      MULind (istot {m-1,n} ())
    end else begin
      MULbas ()
    end // end of [sif]
in
  sif m >= 0 then istot {m,n} () else MULneg (istot {~m,n} ())
end // end of [mul_istot]

(* ****** ****** *)

implement mul_nat_nat_nat (pf) = let
  prfun aux {m,n:nat} {p:int} .<m>.
    (pf: MUL (m, n, p)): [p>=0] void = begin
    case+ pf of MULbas () => () | MULind pf => aux pf
  end // end of [aux]
in
  aux pf
end // end of [mul_nat_nat_nat]

implement mul_negate (pf) = let
  prfn aux {m,n,p:int} (pf: MUL (m, n, p)): MUL (~m, n, ~p) =
    sif m > 0 then MULneg pf
    else sif m < 0 then begin
      let prval MULneg pf = pf in pf end
    end else begin
      let prval MULbas () = pf in pf end
    end // end of [sif]
in
  aux (pf)
end // end of [mul_negate]

prfun mul_m_n1_mnm
  {m,n:int} {p:int} .<max(2*m, 2*(~m)+1)>.
  (pf: MUL (m, n, p)): MUL (m, n+1, p+m) = begin
  case+ pf of
  | MULbas () => MULbas ()
  | MULind pf => MULind (mul_m_n1_mnm pf)
  | MULneg pf => MULneg (mul_m_n1_mnm pf)
end // end of [mul_m_n1_mnm]

prfun mul_m_neg_n_neg_mn
  {m,n:int} {p:int} .<max(2*m, 2*(~m)+1)>.
  (pf: MUL (m, n, p)): MUL (m, ~n, ~p) = begin
  case+ pf of
  | MULbas () => MULbas ()
  | MULind pf => MULind (mul_m_neg_n_neg_mn pf)
  | MULneg pf => MULneg (mul_m_neg_n_neg_mn pf)
end // end of [mul_m_neg_n_neg_mn]

(* ****** ****** *)

implement mul_commute {m,n} (pf) = let
  prfun aux {m:nat;n:int} {p:int} .<m>.
    (pf: MUL (m, n, p)): MUL (n, m, p) = case+ pf of
    | MULbas () => let
        prval pf = mul_istot {n,0} (); prval () = mul_elim pf
      in
        pf
      end // end of [MULbas]
    | MULind pf => mul_m_n1_mnm (aux pf)
  // end of [aux]
in
  sif m >= 0 then aux pf else begin
    let prval MULneg pf = pf in mul_m_neg_n_neg_mn (aux pf) end
  end // end of [sif]
end // end of [mul_commute]

(* ****** ****** *)

implement mul_distribute (pf1, pf2) = let
  prfun aux {m,n1,n2:int} {p1,p2:int} .<max(2*m, 2*(~m)+1)>.
    (pf1: MUL (m, n1, p1), pf2: MUL (m, n2, p2)): MUL (m, n1+n2, p1+p2) =
    case+ (pf1, pf2) of
    | (MULbas (), MULbas ()) => MULbas ()
    | (MULind pf1, MULind pf2) => MULind (aux (pf1, pf2))
    | (MULneg pf1, MULneg pf2) => MULneg (aux (pf1, pf2))
in
  aux (pf1, pf2)
end // end of [mul_distribute]

(* ****** ****** *)

implement mul_associate {x,y,z}
  (pf_xy, pf_yz, pf_xy_z, pf_x_yz) = let
  prfn dist {x1,x2:int;y:int} {x1y,x2y:int}
    (pf1: MUL (x1, y, x1y), pf2: MUL (x2, y, x2y))
    :<prf> MUL (x1+x2, y, x1y+x2y) = let
    prval pf1_ = mul_commute pf1
    prval pf2_ = mul_commute pf2
    prval pf3_ = mul_distribute (pf1_, pf2_)
  in
    mul_commute (pf3_)
  end // end of [dist]

  prfun assoc {x:nat;y,z:int} {xy,yz,xy_z,x_yz:int} .<x>. (
    pf_xy: MUL (x, y, xy)
  , pf_yz: MUL (y, z, yz)
  , pf_xy_z: MUL (xy, z, xy_z)
  , pf_x_yz: MUL (x, yz, x_yz)
  ) :<prf> [xy_z==x_yz] void = begin case+ pf_xy of
  | MULbas () => let
      prval () = mul_elim (pf_xy) // xy = 0
      prval () = mul_elim (pf_xy_z) // xy_y = 0
      prval () = mul_elim (pf_x_yz) // x_yz = 0
    in
      // empty
    end // end of [MULbas]
  | MULind {x1,y,x1y} (pf_x1y) => let // x = x1 + 1; xy = x1y + 1
      prval pf_x1y_z = mul_istot {x1y,z} ()
      prval MULind (pf_x1_yz) = pf_x_yz // x_yz = x + x1_yz
      prval () = assoc (pf_x1y, pf_yz, pf_x1y_z, pf_x1_yz) // x1y_z = x1_yz
      prval pf1_xy_z = dist (pf_x1y_z, pf_yz) // xy_z = x1y_z + yz
      prval () = mul_isfun (pf_xy_z, pf1_xy_z)
    in
      // empty
    end
  end // end of [assoc]
in
  sif x >= 0 then begin
    assoc (pf_xy, pf_yz, pf_xy_z, pf_x_yz)
  end else let
    prval MULneg (pf_xy) = pf_xy
    prval pf_xy_z = mul_negate (pf_xy_z)
    prval MULneg (pf_x_yz) = pf_x_yz
  in
    assoc (pf_xy, pf_yz, pf_xy_z, pf_x_yz)
  end // end of [sif]
end // end of [mul_associate]

(* ****** ****** *)

(*

implement mul_with_cst #{i} #{m,n} (pf0) = let
  prval pf0' = mul_commute pf0
  prval pf1 = mul_make {i,n} ()
  prval pf1' = mul_commute pf1
  prval pf' = mul_distribute (pf0', pf1')
  prval () = mul_elim pf1
in
  mul_commute pf'
end // end of [mul_with_cst]

*)

(* ****** ****** *)

(* greatest common divisors *)

local

prfun aux1 {m,n:pos} {r:int} .<m+n>.
  (pf: GCD (m, n, r)): GCD (n, m, r) =
  sif m <= n then
    let prval GCDind1 pf1 = pf in
       sif m < n then GCDind2 (aux1 pf1) else pf
    end
  else let
    prval GCDind2 pf1 = pf
  in
    GCDind1 (aux1 pf1)
  end // end of [sif]

prfn aux2 {m:nat;n:int} {r:int} 
  (pf: GCD (m, n, r)): GCD (n, m, r) =
  sif n > 0 then
    sif m > 0 then aux1 pf
    else let
      prval GCDbas2 () = pf
    in
      GCDbas1 ()
    end
  else sif n < 0 then let
    prval GCDneg1 pf1 = pf
  in
    sif m > 0 then GCDneg2 (aux1 pf1)
    else let
      prval GCDbas2 () = pf1
    in
      GCDneg2 (GCDbas1 ())
    end
  end else let
    prval GCDbas1 () = pf
  in
    sif m > 0 then GCDbas2 () else pf
  end // end of [sif]

in // in of [local]

// gcd_commute: GCD (m, n, r) -> GCD (n, m, r)
implement gcd_commute {m,n} (pf) =
  sif m >= 0 then aux2 pf
  else let
    prval GCDneg2 pf1 = pf
  in
    sif n >= 0 then GCDneg1 (aux2 pf1)
    else let
      prval GCDneg2 pf2 = aux2 pf1
    in
      GCDneg2 (GCDneg1 pf2)
    end
  end // end of [sif]

end // end of local

(* ****** ****** *)

(* end of [arith.dats] *)
