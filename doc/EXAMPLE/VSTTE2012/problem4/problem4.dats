(*
**
** VSTTE 2012 Verification Competition
** Problem 4
**
*)

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"
//
stadef nil = ilist_nil
stadef cons = ilist_cons
stadef sing = ilist_sing
//
(* ****** ****** *)

datasort tree =
  | leaf of () | node of (tree, tree)
// end of [tree]

datatype tree (tree) =
  | tleaf (leaf) of ()
  | {t1,t2:tree} tnode (node (t1,t2)) of (tree t1, tree t2)
// end of [tree]

(* ****** ****** *)

dataprop
TL (int, tree, ilist) =
  | {d:int}
    TLnil (d, leaf, cons (d, nil)) of ()
  | {d:int} {t1,t2:tree} {xs1,xs2,xs3,xs4:ilist}
    TLcons (d, node (t1, t2), xs4) of (
      TL (d+1,t1,xs1), TL (d+1,t2, xs2), APPEND (xs1, xs2, xs3)
    ) // end [TLcons]
// end of [TL]

propdef
NTL (d:int, t:tree, xs: ilist) = TL (d, t, xs) -<prf> [false] void

(* ****** ****** *)

dataprop
BUILDREC (
  ilist(*source*), ilist(*list consumed*), int (*d*), tree, bool
) =
| {d:int}
  BLDRemp (nil, nil, d, leaf, false)
| {d:int} {h:int | h < d} {xs1:ilist}
  BLDRles (cons (h, xs1), nil, d, leaf, false) of ()
| {d:int} {xs1:ilist}
  BLDRequ (cons (d, xs1), cons (d, nil), d, leaf, true) of ()
| {d:int}{xs,hs:ilist}{t:tree}
  BLDRlft (xs, hs, d, t, false) of
    BUILDREC (xs, hs, d+1, t, false)
| {d:int}{xs,hs,ts,hts,ys:ilist}{t1,t2:tree}
  BLDRrgh (xs, ys, d, node(t1,t2), false) of (
    BUILDREC (xs, hs, d+1, t1, true)
  , BUILDREC (ts, hts, d+1, t2, false)
  , APPEND (hs, ts, xs)
  , APPEND (hs, hts, ys)
  ) // end of [BLDRrgh]
| {xs,hs,ts,hts,tts,ys:ilist} {d:int} {t1,t2:tree}
  BLDRsuc (xs, ys, d, node(t1,t2), true) of (
    BUILDREC (xs, hs, d+1, t1, true)
  , BUILDREC (ts, hts, d+1, t2, true)
  , APPEND (hs, ts, xs)
  , APPEND (hts, tts, ts)
  , APPEND (hs, hts, ys)
  ) // end of [BLDRsuc]
// end of [BUILDREC]

extern
prfun
lemma_buildrec_true_pos
  {d:int} {xs,hs:ilist} {t:tree} (
  pf: BUILDREC (xs, hs, d, t, true)
) : [n:pos] LENGTH (hs, n)

(* ****** ****** *)

dataprop
BUILD (ilist, int, tree, bool) =
| {d:int}{xs,ys:ilist}{t:tree}
  BLDfail_rec (xs, d, t, false) of BUILDREC (xs, ys, d, t, false)
| {d:int}{xs,hs:ilist}{t:tree}{m,n:int | m > n}
  BLDfail_len (xs, d, t, false) of (
    LENGTH (xs, m), LENGTH (hs, n), BUILDREC (xs, hs, d, t, true) 
  ) // end of [BLDfail_len]
| {d:int}{xs:ilist}{t:tree}
  BLDsucc (xs, d, t, true) of BUILDREC (xs, xs, d, t, true)

(* ****** ****** *)

dataprop
ISEMP (ilist, bool) =
  | ISEMPnil (nil, true)
  | {x:int}{xs:ilist} ISEMPcons (cons (x, xs), false)

absviewt@ype list (ilist)
extern
fun list_is_empty {xs: ilist}
  (xs: &list xs):<> [b: bool] (ISEMP (xs, b) | bool b)
extern
fun list_head
  {x:int}{xs1:ilist} (xs: &list (cons (x, xs1))):<> int x
extern
fun list_pop
  {x:int}{xs1:ilist} (xs: &list (cons (x, xs1)) >> list xs1):<> void

(* ****** ****** *)

extern
prfun append_sing
  {x:int}{ys:ilist} (): APPEND (sing(x), ys, cons (x, ys))
extern
prfun append_unit2_elim
  {xs,ys:ilist} (pf: APPEND (xs, nil, ys)): ILISTEQ (xs, ys)
extern
prfun
lemma_append_associate
  {x,y,z:ilist}
  {xy,yz,xy_z,x_yz:ilist} (
  pf1: APPEND (x, y, xy)
, pf2: APPEND (y, z, yz)
, pf3: APPEND (xy, z, xy_z)
, pf4: APPEND (x, yz, x_yz)
) :<prf> ILISTEQ (xy_z,x_yz)

(* ****** ****** *)

extern
fun build_rec
  {d:int} {xs:ilist}{n:nat} (
  pflen: LENGTH (xs, n) | d: int d, xs: &list xs >> list ts
) :<>
  #[ts:ilist][hs:ilist;t:tree;b:bool] (
  BUILDREC (xs, hs, d, t, b), APPEND (hs, ts, xs) | option (tree t, b)
) 

fun bldr_cons
  {d:nat}{x:int}
  {xs1:ilist}{n:nat} .<n,max(0,x-d)>. (
  pflen: LENGTH (cons(x, xs1), n) | d: int d, xs: &list (cons (x, xs1)) >> list ts
) :<>
  #[ts:ilist][hs:ilist;t:tree;ret:bool] (
  BUILDREC (cons(x, xs1), hs, d, t, ret)
, APPEND (hs, ts, cons (x,xs1))
| option (tree t, ret)
) = let
  stadef h = x
  stadef xs = cons (x, xs1)
  val h = list_head (xs) // h: int(x)
in
//
if h < d then let
  prval pf_bld = BLDRles ()
  prval pf_app = append_unit1 {xs} ()
in
  (pf_bld, pf_app | None ())
end else if h = d then let
  val () = list_pop (xs)
  prval pf_bld = BLDRequ ()
  prval pf_app = append_sing {d}{xs1}()
in
  (pf_bld, pf_app | Some (tleaf()))
end else let
  val (pf1_bld, pf1_app | opt) = bldr_cons (pflen | d+1, xs)
in
//
case+ opt of
| None () => (
    BLDRlft (pf1_bld), pf1_app | None ()
  )
| Some (t1) => let
    prval pflen_hs = lemma_buildrec_true_pos (pf1_bld)
    prval pflen_ts = length_istot ()
    prval pflen_xs = append_length_lemma (pf1_app, pflen_hs, pflen_ts)
    prval () = length_isfun (pflen, pflen_xs)
    val (pf2_bld, pf2_app | opt) = build_rec (pflen_ts | d+1, xs)
  in
    case+ opt of
    | None () => let
        prval pf1 = append_istot ()
        prval pf2 = pf2_app
        prval pf3 = append_istot ()
        prval pf4 = pf1_app
        prval ILISTEQ () = lemma_append_associate (pf1, pf2, pf3, pf4)
      in
        (BLDRrgh (pf1_bld, pf2_bld, pf1_app, pf1), pf3 | None ())
      end // end of [None]
    | Some (t2) => let
        prval pf1 = append_istot ()
        prval pf2 = pf2_app
        prval pf3 = append_istot ()
        prval pf4 = pf1_app
        prval ILISTEQ () = lemma_append_associate (pf1, pf2, pf3, pf4)
        prval pf_bld = BLDRsuc (pf1_bld, pf2_bld, pf1_app, pf2_app, pf1)
      in
        (pf_bld, pf3 | Some (tnode(t1, t2)))
      end
  end // end of [Some]
// end of [case]
end (* end of [if] *)
//
end // end of [bldr_cons]

(* ****** ****** *)
////
fun build
  {d:int} {xs:ilist} .<>. (
  d: int d, xs: &list xs >> list ts
) :
  #[ts:ilist][hs:ilist;t:tree;b:bool] (
  BUILD (xs, d, t, b), APPEND (hs, ts, xs) | option (tree t, b)
) = let
  val [hs:ilist,t:tree,ret:bool]
    (pf_bldr, pf_app | opt) = build_rec (d, xs)
  // end of [val]
in
//
case opt of
| None () => (
    BLDfail_rec {d}{xs,hs}{t} (pf_bldr), pf_app | None ()
  ) // end of [None]
| Some (t) => let
    val (pf_emp | isemp) = list_is_empty (xs)
  in
    if isemp then let
      prval ISEMPnil () = pf_emp
      prval ILISTEQ () = append_unit2_elim (pf_app)
    in
      (BLDsucc (pf_bldr), pf_app | Some (t))
    end else let
      prval ISEMPcons () = pf_emp
      prval pflen_hs = length_istot ()
      prval pflen_ts = length_istot ()
      prval pflen_xs = append_length_lemma (pf_app, pflen_hs, pflen_ts)
      prval LENGTHcons _ = pflen_ts
      prval pf_bld = BLDfail_len (pflen_xs, pflen_hs, pf_bldr)
    in
      (pf_bld, pf_app | None ())
    end (* end of [if] *)
  end // end of [Some]
//
end // end of [build]

(* ****** ****** *)

(* end of [problem4.dats] *)
