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

propdef ISCONS (xs:ilist) = ISEMP (xs, false)

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

datasort tree =
 | leaf of () | node of (tree, tree)
// end of [tree]

dataprop
treq (tree, tree) =
  | treq_leaf (leaf, leaf)
  | {t11,t12:tree}{t21,t22:tree}
    treq_node (node (t11, t12), node (t21, t22)) of (treq (t11, t21), treq (t12, t22))
// end of [treq]

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

propdef TL0 (t:tree, xs:ilist) = TL (0, t, xs)

(*
dataprop
NTL (d:int, xs: ilist) =
  {t:tree} NTL (d, xs) of (TL (d, t, xs) -<prf> [false] void)
// end of [NTL]
*)
absprop NTL (d:int, xs:ilist)

extern
prfun lemma_tl_ntl_false
  {d:int}{xs:ilist}{t:tree}
  (pftl: TL (d, t, xs), pfntl: NTL (d, xs)): [false] void
// end of [lemma_tl_ntl_false]

extern
prfun lemma_ntl_empty {d:nat} (): NTL (d, nil)

extern
prfun lemma_ntl_less
  {d:nat} {x:int | x < d}{xs:ilist} (): NTL (d, cons (x, xs))
// end of [lemma_ntl_less]

extern
prfun lemma_ntl_fst
  {d:nat}
  {x:int | x > d}{xs:ilist}
  (pf: NTL (d+1, cons (x, xs))): NTL (d, cons (x, xs))
// end of [lemma_ntl_fst]

extern
prfun lemma_ntl_snd
  {d:nat}
  {xs:ilist}{t:tree}{fs,rs:ilist} (
  pfrem: REMOVE (xs, fs, rs), pftl: TL (d+1, t, fs), pfntl: NTL (d+1, rs)
) : NTL (d, xs)
// end of [lemma_ntl_snd]

extern
prfun lemma_ntl_remainder
  {d:nat}{xs:ilist}{t:tree}{fs,rs:ilist} (
  pfrem: REMOVE (xs, fs, rs), pftl: TL (d, t, fs), pfpos: ISCONS (rs)
) : NTL (d, xs) // end of [lemma_ntl_remainder]

(* ****** ****** *)

extern
prfun
TL_list_isfun
  {d:int}{xs:ilist}{t1,t2:tree} (
  pf1: TL (d, t1, xs), pf2: TL (d, t2, xs)
) : treq (t1, t2)

(* ****** ****** *)
//
abstype list (ilist)
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
  (xs: list (cons (x, xs1))):<> list xs1
//
(* ****** ****** *)

datatype
bldres (
  d:int, xs: ilist, bool
) =
  | {t:tree}{fs,rs:ilist}
    bldres_succ (d, xs, true) of
      (ISCONS(fs), REMOVE (xs, fs, rs), TL (d, t, fs) | tree t, list (rs))
  | bldres_fail (d, xs, false) of (NTL (d, xs) | (*none*))
// end of [bldres]

(* ****** ****** *)

fun build_rec
  {d:nat}{xs:ilist}{n:nat} .<n,1,0>. (
  pflen: LENGTH (xs, n) | d: int d, xs: list xs
) :<> [b:bool] bldres (d, xs, b) = let
  val (pf | isemp) = list_is_empty (xs)
in
//
if isemp then let
  prval ISEMPnil () = pf
  prval pfntl = lemma_ntl_empty ()
in
  bldres_fail (pfntl | (*none*))
end else let
  prval ISEMPcons () = pf in bldr_cons (pflen | d, xs)
end // end of [if]
//
end // end of [build_rec]

and bldr_cons
  {d:nat}{x:int}{xs1:ilist}{n:nat} .<n,0,max(0,x-d)>. (
  pflen: LENGTH (cons(x,xs1), n) | d: int d, xs: list (cons(x, xs1))
) :<> [b:bool] bldres (d, cons(x,xs1), b) = let
  stadef xs = cons (x, xs1)
  val h = list_head (xs) // h: int(x)
in
//
if h < d then let
  prval pfntl = lemma_ntl_less ()
in
  bldres_fail (pfntl | (*none*))
end else if h = d then let
  val xs = list_pop (xs)
  prval pfrem = append_sing {x}{xs1} ()
in
  bldres_succ (ISEMPcons(), pfrem, TLleaf (d) | tleaf (), xs)
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
    prval ISEMPcons () = pf1pos
    prval LENGTHcons _ = pf1len
    prval () = length_isfun (pflen, pflen_alt)
//
    val [b2:bool] res2 = build_rec (pf2len | d+1, xs)
  in
    case+ res2 of
    | bldres_succ (pf2pos, pf2rem, pf2tl | t2, xs) => let
        prval (pfapp, pfrem) = lemma_remove2 (pf1rem, pf2rem)
        prval APPENDcons _ = pfapp
        prval pftl = TLnode (pf1tl, pf2tl, pfapp)
      in
        bldres_succ (ISEMPcons(), pfrem, pftl | tnode (t1, t2), xs)
      end // end of [bldres_succ]
    | bldres_fail (pf2ntl | (*none*)) => let
        prval pfntl = lemma_ntl_snd (pf1rem, pf1tl, pf2ntl)
      in
        bldres_fail (pfntl | (*none*))
      end // end of [bldres_fail]
  end
| bldres_fail (pf1ntl | (*none*)) =>
    bldres_fail (lemma_ntl_fst (pf1ntl) | (*none*))
//
end // end of [if]
//
end // end of [bldr_cons]

(* ****** ****** *)

datatype
buildres (xs: ilist, bool) =
  | {t:tree}
    buildres_succ (xs, true) of (TL0 (t, xs) | tree (t))
  | buildres_fail (xs, false) of (NTL (0, xs) | (*none*))
// end of [buildres]

fun build
  {xs:ilist} .<>. (
  xs: list (xs)
) : [b:bool] buildres (xs, b) = let
  prval pflen = length_istot {xs} ()
  val res = build_rec (pflen | 0, xs)
in
  case+ res of
  | bldres_succ {..}{t} (
      pfpos, pfrem, pftl | t, rs
    ) => let
      val (pfemp | isemp) = list_is_empty (rs)
    in
      if isemp then let
        prval ISEMPnil () = pfemp
        prval ILISTEQ () = append_isfun (pfrem, append_unit2 ())
      in
        buildres_succ (pftl | t)
      end else let
        prval ISEMPcons () = pfemp
        prval pfntl = lemma_ntl_remainder (pfrem, pftl, ISEMPcons())
      in
        buildres_fail (pfntl | (*none*))
      end (* end of [if] *)
    end // end of [bldres_succ]
  | bldres_fail (pfntl | (*none*)) => buildres_fail (pfntl | (*none*))
end // end of [build]

(* ****** ****** *)
//
// The following code is solely for testing
// the functions implemented above; it is not
// needed if you do not want to test.
//
(* ****** ****** *)

extern
fun fprint_tree
  {t:tree} (out: FILEref, t: tree(t)): void
implement
fprint_tree
  (out, t) = case+ t of
  | tnode (t1, t2) => {
      val () = fprint_string (out, "node(")
      val () = fprint_tree (out, t1)
      val () = fprint_string (out, ", ")
      val () = fprint_tree (out, t2)
      val () = fprint_string (out, ")")
    } // end of [tnode]
  | tleaf () => fprint_string (out, "leaf")
// end of [fprint_tree]

(* ****** ****** *)

local

assume list (xs:ilist) = list0 (int)

in

implement
list_is_empty
  (xs) = let
  prval () = __assert () where {
    extern praxi __assert (): [false] void
  }
in
  case+ xs of
  | list0_cons _ => (ISEMPcons | false)
  | list0_nil () => (ISEMPnil () | true)
end // end of [list_is_empty]

implement
list_head
  {x}{xs1} (xs) = let
  val- list0_cons (x, _) = xs
  extern castfn __cast (x:int):<> int(x)
in
  __cast(x)
end // end of [list_head]

implement
list_pop
  {x}{xs1} (xs) = let
  val- list0_cons (_, xs1) = xs in xs1
end // end of [list_pop]

end // end of [local]

(* ****** ****** *)

implement
main () = () where {
//
  stadef t1 = node (leaf, node (node (leaf, leaf), leaf))
  stadef xs1 = cons (1, cons (3, cons (3, cons (2, nil))))
//
  prval pf0 = TLleaf (1)
  prval pf100 = TLleaf (3)
  prval pf101 = TLleaf (3)
  prval pf10 = TLnode (pf100, pf101, APPENDcons (APPENDnil))
  prval pf11 = TLleaf (2)
  prval pf1 = TLnode (pf10, pf11, APPENDcons (APPENDcons (APPENDnil)))
  prval pftl_xs1 = TLnode (pf0, pf1, APPENDcons (APPENDnil)): TL0 (t1, xs1)
//  
  val xs1 = list0_cons (1, list0_cons (3, list0_cons (3, list0_cons (2, list0_nil))))
  val xs1 = __cast (xs1) where {
    extern castfn __cast (xs: list0(int)): list (xs1)
  }
  val res = build (xs1)
  val t_xs1 = case+ res of
    | buildres_succ (pftl | t) => t // HX: it can only succeed
    | buildres_fail (pfntl | (*none*)) =/=> lemma_tl_ntl_false (pftl_xs1, pfntl) 
//
  val () = (print "t_xs1 = "; fprint_tree (stdout_ref, t_xs1); print_newline ())
//
  stadef xs2 = cons (1, cons (3, cons (2, cons (2, nil))))
  val xs2 = list0_cons (1, list0_cons (3, list0_cons (2, list0_cons (2, list0_nil))))
//
} // end of [main]

(* ****** ****** *)

(* end of [problem4.dats] *)
