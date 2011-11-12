(*
**
** VSTTE 2012 Verification Competition
** Problem 4
**
*)

(* ****** ****** *)
//
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
   TLleaf (d, leaf, cons (d, nil)) of int(d)
 | {d:int} {t1,t2:tree} {xs1,xs2,xs3,xs4:ilist}
   TLnode (d, node (t1, t2), xs4) of (
     TL (d+1,t1,xs1), TL (d+1,t2, xs2), APPEND (xs1, xs2, xs3)
   ) // end [TLcons]
// end of [TL]

propdef
NTL (d:int, t:tree, xs: ilist) = TL (d, t, xs) -<prf> [false] void

(* ****** ****** *)
//
abst@ype list (ilist)
//
extern
fun list_is_empty {xs: ilist}
  (xs: list xs):<> [b: bool] (ISEMP (xs, b) | bool b)
extern
fun list_head
  {x:int}{xs1:ilist}
  (xs: list (cons (x, xs1))):<> int x
extern
fun list_pop {x:int}{xs1:ilist}
  (xs: list (cons (x, xs1))): list xs1
//
(* ****** ****** *)

propdef
REMOVE
  (xs:ilist, ys:ilist, zs:ilist) = APPEND (ys, zs, xs)
// end of [REMOVE]

extern
prfun
lemma_remove2
  {xs:ilist}{ys:ilist}{zs:ilist}{zs1:ilist}{zs2:ilist} (
  pf1: REMOVE (xs, ys, zs), pf2: REMOVE (zs, zs1, zs2)
) : [yszs1:ilist] (APPEND (ys, zs1, yszs1), REMOVE (xs, yszs1, zs2))

(* ****** ****** *)

dataprop ISCONS (ilist) = {x:int}{xs:ilist} ISCONS (cons(x,xs))

datatype
bldres (
  d:int, xs: ilist, bool
) =
  | {t:tree}{fs,rs:ilist}
    bldres_succ (d, xs, true) of
      (ISCONS(fs), REMOVE (xs, fs, rs), TL (d, t, fs) | tree t, list (rs))
  | bldres_fail (d, xs, false) of ()
// end of [bldres]

(* ****** ****** *)

fun build_rec
  {d:nat}{xs:ilist}{n:nat} .<n,1,0>. (
  pflen: LENGTH (xs, n) | d: int d, xs: list xs
) : [b:bool] bldres (d, xs, b) = let
  val (pf | isemp ) = list_is_empty (xs)
in
//
if isemp then let
  prval ISEMPnil () = pf in bldres_fail ()
end else let
  prval ISEMPcons () = pf in bldr_cons (pflen | d, xs)
end // end of [if]
//
end // end of [build_rec]

and bldr_cons
  {d:nat}{x:int}{xs1:ilist}{n:nat} .<n,0,max(0,x-d)>. (
  pflen: LENGTH (cons(x,xs1), n) | d: int d, xs: list (cons(x, xs1))
) : [b:bool] bldres (d, cons(x,xs1), b) = let
  stadef xs = cons (x, xs1)
  val h = list_head (xs) // h: int(x)
in
//
if h < d then
  bldres_fail ()
else if h = d then let
  val xs = list_pop (xs)
  prval pfrem = append_sing {x}{xs1} ()
in
  bldres_succ (ISCONS, pfrem, TLleaf (d) | tleaf (), xs)
end else let // h > d
  val [b1:bool] res1 = bldr_cons (pflen | d+1, xs)
in
//
case+ res1 of
| bldres_succ (
    pf1pos, pf1rem, pf1tl | t1, xs
  ) => let
//
    prval pf1len = length_istot ()
    prval pf2len = length_istot ()
    prval pflen_alt = append_length_lemma (pf1rem, pf1len, pf2len)
    prval ISCONS () = pf1pos
    prval LENGTHcons _ = pf1len
    val () = length_isfun (pflen, pflen_alt)
//
    val [b2:bool] res2 = build_rec (pf2len | d+1, xs)
  in
    case+ res2 of
    | bldres_succ (pf2pos, pf2rem, pf2tl | t2, xs) => let
        prval (pfapp, pfrem) = lemma_remove2 (pf1rem, pf2rem)
        prval APPENDcons _ = pfapp
        prval pftl = TLnode (pf1tl, pf2tl, pfapp)
      in
        bldres_succ (ISCONS, pfrem, pftl | tnode (t1, t2), xs)
      end // end of [bldres_succ]
    | bldres_fail () => bldres_fail ()
  end
| bldres_fail () => bldres_fail ()
//
end // end of [if]
//
end // end of [bldr_cons]

(* ****** ****** *)

(* end of [problem4.dats] *)
