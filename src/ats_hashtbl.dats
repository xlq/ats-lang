(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October 2008

(* ****** ****** *)

staload "ats_hashtbl.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

dataviewtype chain (key:t@ype,item:viewt@ype+,int) =
  | {n:nat}
    CHAINcons (key, item, n+1) of (key, item, chain (key, item, n))
  | CHAINnil (key, item, 0)
// end of [chain]

viewtypedef Chain (key: t@ype, item: viewt@ype) = [n:nat] chain (key, item, n)

#define nil CHAINnil; #define cons CHAINcons

fun{key:t@ype;item:t@ype} chain_free
  {n:nat} .<n>. (xs: chain (key, item, n)):<> void = begin
  case+ xs of ~cons (_, _, xs) => chain_free xs | ~nil () => ()
end // end of [chain_free]

fun{key:t@ype;item:t@ype} chain_search {n:nat} .<n>.
  (xs0: !chain (key, item, n), k0: key, eq: (key, key) -<fun> bool)
  :<> Option_vt (item) = begin case+ xs0 of
  | cons (k, i, !xs) => begin
      if eq (k0, k) then begin
        let val ans = Some_vt i in (fold@ xs0; ans) end
      end else begin
        let val ans = chain_search (!xs, k0, eq) in (fold@ xs0; ans) end
      end // end of [if]
    end // end of [cons]
  | nil () => (fold@ xs0; None_vt ()) // end of [nil]
end // end of [chain_search]

fn{key:t@ype;item:viewt@ype} chain_insert {n:nat}
  (xs: &chain (key, item, n) >> chain (key, item, n+1), k: key, i: item)
  :<> void =
  xs := cons (k, i, xs)
// end of [chain_insert]

fun{key:t@ype;item:viewt@ype} chain_remove {n:nat} {l:addr} .<n>.
  (pf: chain (key, item, n) @ l | p0: ptr l, k0: key, eq: (key, key) -<fun> bool)
  :<> [n1:nat | n1 <= n] (chain (key, item, n1) @ l | Option_vt item) = begin
  case+ !p0 of
  | cons (k, !i, !p) => begin
      if eq (k0, k) then let
        val ans = Some_vt !i; val rest = !p
        val () = free@ {key,item} {n} (!p0)
      in
        !p0 := rest; (view@ (!p0) | ans)
      end else let
        val (pf | ans) = chain_remove (view@ (!p) | p, k0, eq)
      in
        fold@ {key,item} (!p0); (view@ (!p0) | ans)
      end
    end // end of [cons]
  | nil () => (fold@ (!p0); (view@ (!p0) | None_vt ()))
end // end of [chain_remove]

(* ****** ****** *)

viewtypedef table (key: t@ype, item: viewt@ype, sz: int) = @[Chain(key,item)][sz]

fn{key:t@ype;item:t@ype} table_search {sz:nat}
  (tbl: &table (key, item, sz), off: natLt sz, k0: key, eq: (key, key) -<fun> bool)
  :<> Option_vt item = let
  viewtypedef elt = Chain(key,item)
  val off_sz = size1_of_int1 (off)
  val (pf1, pf2 | p) =
    array_ptr_takeout_tsz {elt} (view@ tbl | &tbl, off_sz, sizeof<elt>)
  val ans = chain_search (!p, k0, eq)
  prval () = view@ tbl := pf2 (pf1)
in
  ans
end // end of [table_search]

fn{key:t@ype;item:viewt@ype} table_insert {sz:nat}
  (tbl: &table (key, item, sz), off: natLt sz, k: key, i: item)
  :<> void = let
  viewtypedef elt = Chain(key,item)
  val off_sz = size1_of_int1 (off)
  val (pf1, pf2 | p) =
    array_ptr_takeout_tsz {elt} (view@ tbl | &tbl, off_sz, sizeof<elt>)
  val () = chain_insert (!p, k, i)
  prval () = view@ tbl := pf2 (pf1)
in
  // empty
end // end of [table_insert]

fn{key:t@ype;item:viewt@ype} table_remove {sz:nat}
  (tbl: &table (key, item, sz), off: sizeLt sz, k: key, eq: (key, key) -<fun> bool)
  :<> Option_vt (item) = let
  viewtypedef elt = Chain(key,item)
  val (pf1, pf2 | p) =
    array_ptr_takeout_tsz {elt} (view@ tbl | &tbl, off, sizeof<elt>)
  val (pf1 | ans) = chain_remove (pf1 | p, k, eq)
  prval () = view@ tbl := pf2 (pf1)
in
  ans
end // end of [table_remove]

extern fun table_chain_get
  {key:t@ype;item:viewt@ype} {sz,n:nat | n < sz}
  (tbl: &table (key, item, sz), off: int n):<> Chain (key, item)

implement table_chain_get {key,item} (tbl, off) = let
  viewtypedef elt = Chain(key,item)
  val off_sz = size1_of_int1 (off)
  val (pf1, pf2 | p) =
    array_ptr_takeout_tsz {elt} (view@ tbl | &tbl, off_sz, sizeof<elt>)
  val ans = !p
  val () = !p := nil ()
  prval () = view@ tbl := pf2 (pf1)
in
  ans
end // end of [table_chain_get]

(* ****** ****** *)

viewtypedef
hashtbl_struct (
  key:t@ype, item:viewt@ype, sz:int
) = @{
  hash= key -<fun> uint
, eq= (key, key) -<fun> bool
, size= int sz
, nitm= int
, table= table (key, item, sz)
} // end of [hashtbl_struct]

stadef HT = hashtbl_struct

fn{key:t@ype;item:t@ype} ht_search {sz:pos}
  (ht: &HT (key, item, sz), k0: key):<> Option_vt item = let
  val off = op uimod (ht.hash k0, ht.size)
in
  table_search (ht.table, off, k0, ht.eq)
end // end of [ht_search]

fn{key:t@ype;item:viewt@ype} ht_insert {sz:pos}
  (ht: &HT (key, item, sz), k: key, i: item):<> void = let
  val off = op uimod (ht.hash k, ht.size)
in
  table_insert (ht.table, off, k, i); ht.nitm := ht.nitm + 1
end // end of [ht_insert]

fun{key:t@ype;item:viewt@ype}
  ht_insert_chain {sz:pos} {n:nat} .<n>.
  (ht: &HT (key, item, sz), kis: chain (key, item, n))
  :<> void = begin case+ kis of
  | ~cons (k, i, kis) => begin
      ht_insert<key,item> {sz} (ht, k, i); 
      ht_insert_chain (ht, kis)
    end // end of [cons]
  | ~nil () => () // end of [nil]
end // end of [ht_insert_chain]

fn{key:t@ype;item:viewt@ype} ht_remove {sz:pos}
  (ht: &HT (key, item, sz), k: key):<> Option_vt item = let
  val off = op uimod (ht.hash k, ht.size)
  val off_sz = size1_of_int1 (off)
  val ans = table_remove<key,item> (ht.table, off_sz, k, ht.eq)
  val () = (case+ ans of
    | Some_vt !i => (fold@ ans; ht.nitm := ht.nitm - 1)
    | None_vt () => fold@ ans
  ) : void // end of [val]
in
  ans
end // end of [ht_remove]

(* ****** ****** *)

extern fun htp_make {key:t@ype;item:viewt@ype} {sz:pos}
  (hash: key -<fun> uint, eq: (key, key) -<fun> bool, sz: int sz)
  :<> [l:addr | l <> null] (HT (key, item, sz) @ l | ptr l)
  = "ats_htp_make"

// should only be called if all chains are empty!
extern fun __htp_free
  {key:t@ype;item:viewt@ype} {sz:nat} {l:addr}
  (pf: HT (key,item,sz) @ l | p: ptr l):<> void
  = "__ats_htp_free"

extern typedef "hashtbl_struct" =
  [key:t@ype;item:viewt@ype] [sz:int] HT (key, item, sz)
extern val "CHAINnil" = CHAINnil ()
extern typedef "chain" =
  [key:t@ype;item:viewt@ype] Chain (key, item)

%{$

ats_ptr_type
ats_htp_make (
  ats_ptr_type hash, ats_ptr_type eq, ats_int_type sz
) {
  int n ;
  hashtbl_struct *htp ;
  htp = ATS_MALLOC (sizeof(hashtbl_struct) + sz * sizeof(chain)) ;

  htp->atslab_hash = hash ;
  htp->atslab_eq = eq ;
  htp->atslab_size = sz ;
//
  for (n = 0 ; n < sz ; ++n) { htp->atslab_table[n] = CHAINnil ; }
//  
  return htp ;
} // end of [ats_htp_make]

ats_void_type
__ats_htp_free (
  ats_ptr_type htp
) {
  ATS_FREE (htp) ; return ;
} // end of [__ats_htp_free]

%} // end of [%{$]

(* ****** ****** *)

fn{key:t@ype;item:t@ype}
  htp_clear {sz:nat} {l:addr}
    (pf: HT (key,item,sz) @ l | p: ptr l):<> void = let
  val sz = p->size
  fun loop {n:nat | n <= sz} .<sz-n>.
    (pf: !HT (key,item,sz) @ l | p: ptr l, off: int n):<> void =
    if off < sz then let
      val kis = table_chain_get (p->table, off)
    in
      chain_free kis; loop (pf | p, off + 1)
    end
  val () = loop (pf | p, 0)
in
  __htp_free (pf | p)
end // end of [htp_clear]

fn{key:t@ype;item:viewt@ype}
  htp_resize {sz1,sz2:pos} {l1:addr}
    (pf1: HT (key,item,sz1) @ l1 | p1: ptr l1, sz2: int sz2):<>
    [l2:addr | l2 <> null] (HT (key,item,sz2) @ l2 | ptr l2) = let
  val sz1 = p1->size
  val (pf2 | p2) = htp_make {key,item} (p1->hash, p1->eq, sz2)
  fun loop {n:nat | n <= sz1} .<sz1-n>.
    (pf1: !HT (key,item,sz1) @ l1 | sz1: int sz1,
     p1: ptr l1, hashtbl2: &HT (key,item,sz2), off: int n):<> void = begin
    if off < sz1 then let
      val kis = table_chain_get (p1->table, off)
      val () = ht_insert_chain (hashtbl2, kis)
    in
      loop (pf1 | sz1, p1, hashtbl2, off + 1)
    end
  end // end of [loop]
  val () = loop (pf1 | sz1, p1, !p2, 0)
  val () = __htp_free (pf1 | p1)
in
  (pf2 | p2)
end // end of [htp_resize]

(* ****** ****** *)

viewtypedef hashtbl_ptr (key:t@ype,item:viewt@ype) =
  [sz:pos] [l:addr] (option_v (HT (key, item, sz) @ l, l <> null) | ptr l)
// end of [hashtbl_ptr]

assume hashtbl_t (key:t@ype,item:viewt@ype) = ref (hashtbl_ptr (key, item))

(* ****** ****** *)

implement hashtbl_make_hint
  {key,item} {sz} (hash, eq, hint) = let
  val [l:addr] (pf_htp | htp) =
    htp_make {key,item} {sz} (hash, eq, hint)
  prval pfopt_htp =
    (Some_v pf_htp): option_v (HT (key, item, sz) @ l, l <> null)
  viewtypedef T = hashtbl_ptr (key, item)
in
  ref_make_elt<T> @(pfopt_htp | htp)
end // end of [hashtbl_make_hint]

implement hashtbl_str_make_hint (hint) = let
  val hashfn = lam (x: string): uint =<fun> uint_of_ulint (string_hash_33 x)
in
  hashtbl_make_hint (hashfn, eq_string_string, hint)
end // end of [hashtbl_str_make_hint]

(* ****** ****** *)

implement{key,item} hashtbl_clear (hashtbl) = let
  val (vbox pf | htpp) = ref_get_view_ptr (hashtbl)
  val (pf_htp_opt | htp) = !htpp
in
  if htp <> null then let
    prval Some_v pf_htp = pf_htp_opt
    val () = htp_clear (pf_htp | htp)
    viewdef V = HT (key,item,1) @ null
    prval () = pf_htp_opt := None_v {V} ()
  in
    !htpp := (pf_htp_opt | null)
  end else begin
    !htpp := (pf_htp_opt | htp)
  end // end of [if]
end // end of [hashtbl_clear]

(* ****** ****** *)

implement{key,item} hashtbl_search (hashtbl, k) = let
  val (vbox pf | htpp) = ref_get_view_ptr (hashtbl)
  val (pf_htp_opt | htp) = !htpp
in
  if htp <> null then let
    prval Some_v pf_htp = pf_htp_opt
    val ans = ht_search (!htp, k)
    prval () = pf_htp_opt := Some_v pf_htp
    val () = !htpp := (pf_htp_opt | htp)
  in
    ans
  end else let
    val () = !htpp := (pf_htp_opt | htp)
  in
    None_vt ()
  end // end of [if]
end // end of [hashtbl_search]

(* ****** ****** *)

#define THRESHOLD 5

implement{key,item} hashtbl_insert (hashtbl, k, i) = let
  val (vbox pf | htpp) = ref_get_view_ptr (hashtbl)
  val (pf_htp_opt | htp) = !htpp
in
  if htp <> null then let
    prval Some_v pf_htp = pf_htp_opt
    val sz = htp->size and nitm = htp->nitm
  in
    if nitm < sz * THRESHOLD then let
      val () = ht_insert (!htp, k, i)
      prval () = pf_htp_opt := Some_v pf_htp
      val () = !htpp := (pf_htp_opt | htp)
    in
      None_vt ()
    end else let
      val (pf_htp | htp) = htp_resize (pf_htp | htp, sz + sz)
      val () = ht_insert (!htp, k, i)
      prval () = pf_htp_opt := Some_v pf_htp
      val () = !htpp := (pf_htp_opt | htp)
    in
      None_vt ()
    end
  end else begin
    (!htpp := (pf_htp_opt | htp); Some_vt i)
  end // end of [if]
end // end of [hashtbl_insert]

implement{key,item} hashtbl_remove (hashtbl, k) = let
  val (vbox pf | htpp) = ref_get_view_ptr (hashtbl)
  val (pf_htp_opt | htp) = !htpp
in
  if htp <> null then let
    prval Some_v pf_htp = pf_htp_opt
    val ans = ht_remove (!htp, k)
    prval () = pf_htp_opt := Some_v pf_htp
    val () = !htpp := (pf_htp_opt | htp)
  in
    ans
  end else let
    val () = !htpp := (pf_htp_opt | htp)
  in
    None_vt ()
  end // end of [if]
end // end of [hashtbl_remove]

(* ****** ****** *)

(* end of [ats_hashtbl.dats] *)
