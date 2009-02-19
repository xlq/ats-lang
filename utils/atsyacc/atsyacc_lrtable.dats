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

staload "symbol.sats"
staload "token.sats"
staload "grammar.sats"

(* ****** ****** *)

staload "atsyacc_top.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/DATS/lazy_vt.dats"
staload _(*anonymous*) = "prelude/DATS/list_vt.dats"
staload _(*anonymous*) = "prelude/DATS/pointer.dats"
staload _(*anonymous*) = "prelude/DATS/reference.dats"
staload _(*anonymous*) = "prelude/DATS/slseg.dats"

(* ****** ****** *)

typedef lritem (n:int, i:int) = '{
  lritem_lhs= symbol_t
, lritem_rhs= rulerhs_t n
, lritem_ind= int i
}

typedef lritem = [n,i:nat | i <= n] lritem (n, i)

//

extern fun lritem_make {n,i:nat | i <= n}
  (lhs: symbol_t, rhs: rulerhs_t n, ind: int i): lritem (n, i)

implement lritem_make (lhs, rhs, ind) = '{
  lritem_lhs= lhs, lritem_rhs= rhs, lritem_ind= ind
}

//

extern fun lritem_nrhs_get (itm: lritem):<> int

implement lritem_nrhs_get (itm) = let
  val rhs = itm.lritem_rhs in rulerhs_num_get (rhs)
end // end of [lritem_nrhs_get]

extern
fun compare_lritem_lritem (itm1: lritem, itm2: lritem):<> Sgn
overload compare with compare_lritem_lritem

implement compare_lritem_lritem (itm1, itm2) = let
  val nrhs1 = lritem_nrhs_get itm1
  and nrhs2 = lritem_nrhs_get itm2
  val sgn1 = compare_int_int (nrhs1, nrhs2)
in
  if sgn1 <> 0 then sgn1 else
    compare_int_int (itm1.lritem_ind, itm2.lritem_ind)
  // end of [if]
end // end of [compare_lritem_lritem]

(* ****** ****** *)

fun fprint_lritem_rhs
  {m:file_mode} {n,i:nat | i <= n} (
    pf_mod: file_mode_lte (m, w)
  | out: &FILE m, rhs: rulerhs_t n, ind: int i
  ) : void = let
  val nsym = rulerhs_nsym_get (rhs)
  val alpha = rulerhs_symarr_get (rhs)
  fun loop {i:nat | i <= n}
    (out: &FILE m, i: int i, j: &int)
    :<cloref1> void = let
    val () = if (i = ind) then let
      val () = if (j > 0) then fprint_char (pf_mod | out, ' ')
      val () = j := j + 1
    in
      fprint_char (pf_mod | out, '.')
    end // end of [val]
  in
    if i < nsym then let
      val X = alpha[i]
      val () = if j > 0 then fprint_char (pf_mod | out, ' ')
      val () = j := j + 1
      val () = fprint_symbol (pf_mod | out, X)
    in
      loop (out, i + 1, j)
    end // end of [if]
  end (* end of [loop] *)
in
  loop (out, 0, j) where { var j: int = 0 }
end // end of [fprint_lritem_rhs]

extern fun fprint_lritem {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, itm: lritem): void

implement fprint_lritem (pf_mod | out, itm) = let
  val lhs = itm.lritem_lhs
  val () = fprint_symbol (pf_mod | out, lhs)
  val () = fprint_string (pf_mod | out, " : ")
  val () = fprint_lritem_rhs (
    pf_mod | out, itm.lritem_rhs, itm.lritem_ind
  ) // end of [val]
in
  // empty
end // end of [fprint_lritem]

extern fun print_lritem (itm: lritem): void
extern fun prerr_lritem (itm: lritem): void

implement print_lritem (itm) = print_mac (fprint_lritem, itm)
implement prerr_lritem (itm) = prerr_mac (fprint_lritem, itm)

(* ****** ****** *)

staload M = "LIB/funmap_avltree.dats"

abstype lrstate_t // for representing LR(1)-states

typedef lrmap = $M.map_t (lritem, symbolset_t)
typedef lrlst = List @(lritem, symbolset_t)
viewtypedef lrlst_vt = List_vt @(lritem, symbolset_t)

typedef lrgotolst = List @(symbol_t, lrstate_t)

(* ****** ****** *)

extern fun fprint_lrlst {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, lst: lrlst): void

implement fprint_lrlst {m}
  (pf_mod | out, lst) = loop (out, lst) where {
  fun loop (out: &FILE m, xs: lrlst): void = case+ xs of
    | list_cons (x, xs) => let
        val () = fprint_lritem (pf_mod | out, x.0)
        val () = fprint_newline (pf_mod | out) in loop (out, xs)
      end // end of [fprint_lrlst]
    | list_nil () => ()
} // end of [fprint_lrlst]

(* ****** ****** *)

extern fun fprint_lrmap {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, map: lrmap): void

implement fprint_lrmap {m}
  (pf_mod | out, map) = loop (out, xs) where {
  typedef keyitm = @(lritem, symbolset_t)
  fun loop (out: &FILE m, xs: stream_vt keyitm): void = case+ !xs of
    | ~stream_vt_cons (x, xs) => let
        val () = fprint_lritem (pf_mod | out, x.0)
        val () = fprint_newline (pf_mod | out) in loop (out, xs)
      end // end of [fprint_lrlst]
    | ~stream_vt_nil () => ()
  val xs = $M.funmap_make_stream_key_itm (map)
} // end of [fprint_lrlst]

extern fun print_lrmap (itm: lrmap): void
extern fun prerr_lrmap (itm: lrmap): void

implement print_lrmap (itm) = print_mac (fprint_lrmap, itm)
implement prerr_lrmap (itm) = prerr_mac (fprint_lrmap, itm)

(* ****** ****** *)

extern
fun lrmap_nil (): lrmap

extern
fun lrmap_search (map: lrmap, k: lritem): Option_vt (symbolset_t)

extern
fun lrmap_insert (map: lrmap, k: lritem, xs: symbolset_t): lrmap

extern
fun lrmap_remove (map: lrmap, k: lritem): lrmap

local

val _cmp = lam
  (k1: lritem, k2: lritem): Sgn =<cloref> compare (k1, k2)

in

implement lrmap_nil () = $M.funmap_empty<> ()

implement lrmap_search (map, k) = $M.funmap_search (map, k, _cmp)

implement lrmap_insert (map, k, xs) = $M.funmap_insert (map, k, xs, _cmp)

implement lrmap_remove (map, k) = $M.funmap_remove (map, k, _cmp)

end // end of [local]

//

extern
fun lrstate_num_get (st: lrstate_t): int

extern
fun lrstate_num_set (st: lrstate_t, num: int): void
  = "atsyacc_lrstate_num_set"

extern
fun lrstate_lst_get (st: lrstate_t): lrlst

extern
fun lrstate_gotolst_get (st: lrstate_t): lrgotolst

extern
fun lrstate_gotolst_set (st: lrstate_t, gts: lrgotolst): void

extern fun lrstate_make (num: int, lst: lrlst): lrstate_t

(* ****** ****** *)

fn lrlst_make_lrmap (map: lrmap): lrlst = kis where {
  typedef keyitm = @(lritem, symbolset_t)
  val kis = $M.funmap_make_stream_key_itm (map)
  val (_(*n*), kis) = list_vt_of_stream_vt<keyitm> (kis)
  val kis = list_of_list_vt (kis)
} // end of [lrlst_make_lrmap]

//

extern
fun eqkey_lrlst_lrlst (lst1: lrlst, lst2: lrlst):<> bool

implement eqkey_lrlst_lrlst (lst1, lst2) = let
  fun _eqkey (kis1: !lrlst, kis2: !lrlst): bool =
    case+ (kis1, kis2) of
    | (list_cons (ki1, !p_kis1),
       list_cons (ki2, kis2)) => begin
        if compare (ki1.0, ki2.0) <> 0 then false else _eqkey (kis1, kis2)
      end (* end of [list_cons, list_cons] *)
    | (list_nil (), list_nil ()) => true
    | (_, _) => false
  // end of [_eqkey]
in
  $effmask_all (_eqkey (lst1, lst2))
end // end of [eqkey_lrlst_lrlst]

//

extern fun lrlst_hash (kis: lrlst):<> uint

implement lrlst_hash (kis) = let
  fun loop (kis: lrlst, h: uint): uint =
    case+ kis of
    | list_cons (ki, kis) => let
        val key = ki.0
        val nhrs = lritem_nrhs_get (key)
        val h = (h << 5) + h + (uint_of_int nhrs)
        val h = (h << 5) + h + (uint_of_int key.lritem_ind)
      in
        loop (kis, h)
      end // end of [list_vt_cons]
    | list_nil () => h
  // end of [loop]
in
  $effmask_all (loop (kis, 31415926U))
end // end of [lrlst_hash]

(* ****** ****** *)

local

typedef lrstate = '{
  lrstate_num= int
, lrstate_lst= lrlst
, lrstate_gotolst = lrgotolst
} // end of [lrstate]

extern castfn lrstate_intr (x: lrstate): lrstate_t
extern castfn lrstate_elim (x: lrstate_t): lrstate

in // in of [local]

extern typedef "lrstate_t" = lrstate

implement lrstate_num_get (st) = let
  val st = lrstate_elim (st) in st.lrstate_num
end // end of [lrstate_num_get]

implement lrstate_lst_get (st) = let
  val st = lrstate_elim (st) in st.lrstate_lst
end // end of [lrstate_lst_get]

implement lrstate_gotolst_get (st) = let
  val st = lrstate_elim (st) in st.lrstate_gotolst
end // end of [lrstate_gotolst_get]

implement lrstate_make (num, lst) = lrstate_intr '{
  lrstate_num= num
, lrstate_lst= lst // [map] is required to be a closure
, lrstate_gotolst= list_nil () (* a place holder *)
} // end of [lrstate_make]

end // end of [local]

(* ****** ****** *)

staload H = "LIB/hashtable.dats"

extern fun lrlst_insert (lst: lrlst): void

local

typedef key = lrlst; typedef itm = lrstate_t

val the_lrlst_table = let
  val hfn = lam (x: lrlst): uint =<cloref> lrlst_hash (x)
  val efn = lam
    (x1: lrlst, x2: lrlst): bool =<cloref> eqkey_lrlst_lrlst (x1, x2)
in
  $H.hashtbl_make<key,itm> (hfn, efn)
end // end of [the_lrlst_table]

in

implement lrlst_insert (lst) = let
  val ost1 = $H.hashtbl_search (the_lrlst_table, lst)
  val () = case+ ost1 of
    | ~Some_vt st1 => let
        // this is a bit risky and innovative :)
        extern castfn lstcast_to (lst: lrlst): lrlst_vt
        extern castfn lstcast_of (lst: lrlst_vt): lrlst
        val lst0 = lstcast_to (lst)
        val lst1 = lrstate_lst_get (st1)
        val () = loop (lst0, lst1) where {
          fun loop (kis0: !lrlst_vt, kis1: lrlst): void =
            case+ kis0 of
            | list_vt_cons (!p_ki0, !p_kis0) => begin case+ kis1 of
              | list_cons (ki1, kis1) => let
                  val ki0_1 = p_ki0->1
                  val () = p_ki0->1 := symbolset_union (ki0_1, ki1.1)
                in
                  fold@ kis0
                end // end of [let]
              | list_nil () => (fold@ kis0)
              end // end of [list_vt_cons]
            | list_vt_nil () => (fold@ kis0)
        } // end of [val]
        val lst = lstcast_of (lst0)
      in
        // empty
      end // end of [Some_vt]
    | ~None_vt () => let
        val st = lrstate_make (0, lst)
        val ans = $H.hashtbl_insert_err<key,itm> (the_lrlst_table, lst, st)
        val () = case+ ans of ~Some_vt _ => () | ~None_vt () => ()
      in
        // empty
      end // end of [None_vt]
  // end of [val]
in
  // empty
end // end of [lrlst_insert]

end // end of [local]

(* ****** ****** *)

fun symarr_frstset_gen
  {n:nat} {lb,ub:nat | lb <= ub; ub <= n}
  (alpha: symarr n, lb: int lb, ub: int ub, nullable: &bool)
  : symbolset_t = let
  fun loop {lb,ub:nat | lb <= ub; ub <= n} .<ub-lb>.
    (lb: int lb, ub: int ub, res: symbolset_t, nullable: &bool)
    :<cloref1> symbolset_t =
    if lb < ub then let
      val x = alpha[lb]
      val res = symbolset_union (res, symbol_frstset_get x)
    in
      if symbol_nullable_get x then loop (lb+1, ub, res, nullable) else res
    end else begin
      nullable := true; res
    end // end of [if]
  // end of [loop]
in
  loop (lb, ub, symbolset_nil, nullable)
end // end of [symarr_frstset_gen]

(* ****** ****** *)

staload Q = "LIB/linqueuelst.dats"

fun lrmap_closure_gen (map0: lrmap): lrmap = let
  typedef key = lritem and itm = symbolset_t
  viewtypedef keyque = [n:nat] $Q.linqueuelst_vt (key, n)
  var que_r: keyque = $Q.linqueuelst_nil<> {key} ()
  viewdef V = keyque @ que_r
  val () = $M.funmap_foreach_clo {V}
    (view@ que_r | map0, !p_clo) where { var !p_clo = @lam
    (pf: !V | k: key, _: itm): void => $Q.linqueuelst_enqueue (que_r, k)
  } // end of [val]
  var map_r: lrmap = map0
  val () = while ($Q.linqueuelst_is_cons que_r) let
    val key = $Q.linqueuelst_dequeue que_r // itm = alpha . X beta
// (*
    val () = begin
      print "lrmap_closure_gen: while: key = "; print_lritem key; print_newline ()
    end // end of [val]
// *)
    val ind = key.lritem_ind; val rhs = key.lritem_rhs
    val nsym = rulerhs_nsym_get rhs
// (*
    val () = begin
      print "lrmap_closure_gen: while: ind = "; print ind; print_newline ();
      print "lrmap_closure_gen: while: nsym = "; print nsym; print_newline ();
    end // end of [val]
// *)
  in
    if ind < nsym then let
      val symarr = rulerhs_symarr_get rhs
      val X = symarr[ind]; val X_rhss = symbol_rulerhslst_get (X)
(*
      val () = begin
        print "lrmap_closure_gen: while: X = "; print_symbol X; print_newline ();
      end // end of [val]
*)
    in
      case+ X_rhss of
      | list_cons _ => loop_if
          (que_r, map_r, X, X_rhss, xs) where {
          val xs = if ~nullable then xs else let
            val oxs1 = lrmap_search (map_r, key) in case+ oxs1 of
              | ~Some_vt xs1 => symbolset_union (xs, xs1) | ~None_vt () => xs
          end : itm where {
            var nullable: bool = false
            val xs = symarr_frstset_gen (symarr, ind + 1, nsym, nullable)
          } // end of [val]
(*
          val () = begin
            print "lrmap_closure_gen: while: xs = "; print_symbolset xs; print_newline ();
          end // end of [val]
*)
          fun loop (
              que_r: &keyque, map_r: &lrmap
            , lhs: symbol_t, rhss: rulerhslst, xs: symbolset_t
            ) : void = case+ rhss of
            | list_cons (rhs, rhss) => let
                val () = begin
                  print "bef: map_r = begin\n"; print_lrmap map_r; print "end\n"
                end // end of [val]
                val key0 = lritem_make (lhs, rhs, 0)
                val oxs0 = lrmap_search (map_r, key0)
                var flag: int = 0; val xs0 = (case+ oxs0 of
                  | ~Some_vt xs0 => xs0 where {
                      val xs0 = symbolset_union_flag (xs0, xs, flag)
                      val () = begin
                        if flag > 0 then map_r := lrmap_remove (map_r, key0)
                      end // end of [val]
                    } // end of [Some_vt]
                  | ~None_vt () => (flag := 1; xs)
                ) : itm // end of [val]
                val () = begin
                  print "aft_rmv: map_r = begin\n"; print_lrmap map_r; print "end\n"
                end // end of [val]
                val () = if flag > 0 then let
                  val () = map_r := lrmap_insert (map_r, key0, xs0)
                  val () = begin
                    print "lrmap_insert: key0 = "; print_lritem key0; print_newline ()
                  end // end of [val]
                in
                  $Q.linqueuelst_enqueue (que_r, key0)
                end // end of [if]
                val () = begin
                  print "aft_ins: map_r = begin\n"; print_lrmap map_r; print "end\n"
                end // end of [val]
              in
                loop (que_r, map_r, lhs, rhss, xs)
              end // end of [list_cons]
            | list_nil () => ()
          // end of [loop]

          fn loop_if (
              que_r: &keyque, map_r: &lrmap
            , lhs: symbol_t, rhss: rulerhslst, xs: symbolset_t
            ) : void = begin
            if symbolset_isnot_nil xs then
               loop (que_r, map_r, lhs, rhss, xs)
          end // end of [loop_if]
        } // end of [list_cons]
      | list_nil () => ()
    end // end of [if]
  end (* end of [while] *)
  val () = $Q.linqueuelst_free<key> (que_r)
in
  map_r // the computed closure of [map] *)
end (* end of [lrmap_closure] *)

(* ****** ****** *)

extern
fun the_first_lritem_gen (): lritem 

implement the_first_lritem_gen () = let
  val lhs = the_accept_symbol
  val rhss = symbol_rulerhslst_get (lhs)
  val rhs = (case+ rhss of
    | list_cons (rhs, _) => rhs | list_nil () => begin
        prerr "error(INTERNAL): the_first_lritem"; prerr_newline ();
        exit {rulerhs_t} (1)
      end // end of [list_nil]
  ) : rulerhs_t
in
  lritem_make (lhs, rhs, 0)
end // end of [the_first_lritem_gen]

(* ****** ****** *)

implement the_lrtable_gen () = let
  val map = lrmap_nil ()
  val itm = the_first_lritem_gen ()
  val map = lrmap_insert (map, itm, symbolset_nil)
  val () = print "lrmap_closure_gen: bef\n"
  val () = print_lrmap (map)
  val map = lrmap_closure_gen (map)
  val () = print "lrmap_closure_gen: aft\n"
  val () = print_lrmap (map)
in
  // empty
end // end of [the_lrtable_gen]

(* ****** ****** *)

%{$

ats_void_type
atsyacc_lrstate_num_set
  (ats_ptr_type st, ats_int_type num) {
  ((lrstate_t)st)->atslab_lrstate_num = num ; return ;
}

ats_void_type
atsyacc_lrstate_gotolst_set
  (ats_ptr_type st, ats_ptr_type gts) {
  ((lrstate_t)st)->atslab_lrstate_gotolst = gts ; return ;
}

%}

(* ****** ****** *)

(* end of [grammar.dats] *)
