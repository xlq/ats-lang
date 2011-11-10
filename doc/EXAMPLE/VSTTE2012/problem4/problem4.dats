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
| {d:int}{t:tree}
 BLDRemp (nil, nil, d, t, false)
| {d:int} {h:int | h < d}
 {xs1:ilist} {t:tree}
 BLDRles (cons (h, xs1), nil, d, t, false) of ()
| {d:int} {xs1:ilist}
 BLDRequ (cons (d, xs1), cons (d, nil), d, leaf, true) of ()
| {d:int}{xs,fs:ilist}{t:tree}
 BLDRlft (xs, fs, d, t, false) of
   BUILDREC (xs, fs, d+1, t, false)
| {d:int}{xs,hs,ts,hts,ys:ilist}{t1,t2:tree}
 BLDRrgh (xs, ys, d, node(t1,t2), false) of (
   BUILDREC (xs, hs, d+1, t1, true)
 , BUILDREC (ts, hts, d+1, t2, false)
 , APPEND (hs, ts, xs)
 , APPEND (hs, hts, ys)
 )
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
//
absviewt@ype list (ilist)
//
extern
fun list_is_empty {xs: ilist}
 (xs: &list xs):<> [b: bool] (ISEMP (xs, b) | bool b)
extern
fun list_head
 {x:int}{xs1:ilist} (xs: &list (cons (x, xs1))):<> int x
extern
fun list_pop
 {x:int}{xs1:ilist} (xs: &list (cons (x, xs1)) >> list xs1):<> void
//
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

fun bldr_cons
 {d:nat}{x:int}
 {xs1:ilist}{n:nat} .<n, max(0,x-d)>. (
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
 prval pf_bld = BLDRles{d}{h}{xs1}{leaf} ()
 prval pf_app = append_unit1 {xs} ()
in
 (pf_bld, pf_app | None ())
end else if h = d then let
 val () = list_pop (xs)
 prval pf_bld = BLDRequ {d}{xs1} ()
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
   
  val (pf_emp | b) = list_is_empty (xs)
in
 if b = true then let
   prval ISEMPnil () = pf_emp
   prval pf2_bld = BLDRemp ()
   prval pf1 = append_istot ()
   prval pf2 = append_unit1 ()
   prval pf3 = append_istot ()
   prval pf4 = pf1_app
   prval ILISTEQ () = lemma_append_associate (pf1, pf2, pf3, pf4)
 in 
   (BLDRrgh (pf1_bld, pf2_bld, pf1_app, pf1), pf3 | None ())
 end else let
   prval ISEMPcons () = pf_emp
   val (pf2_bld, pf2_app | opt) = bldr_cons (pflen_ts | d+1, xs)
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
  end // end of [case]
 end // end of [Some]
// end of [case]
end (* end of [if] *)
//
end // end of [bldr_cons]

fun build_rec
 {d:nat} {xs:ilist} .<>. (
 d: int d, xs: &list xs >> list ts
) :<>
 #[ts:ilist][hs:ilist;t:tree;b:bool] (
 BUILDREC (xs, hs, d, t, b), APPEND (hs, ts, xs) | option (tree t, b)
) = let 
  val (pf_emp | isemp) = list_is_empty (xs)
in
  if isemp then let
    prval ISEMPnil () = pf_emp
  in
    (BLDRemp {..}{leaf} (), append_unit1 () | None ())
  end else let
    prval ISEMPcons () = pf_emp
  in
    bldr_cons (length_istot () | d, xs)
  end
end

(* ****** ****** *)

fun build
 {d:nat} {xs:ilist} .<>. (
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

(* auxilliary *)
extern prfun lemma_buildrec_part {xs,hs:ilist} {d:int}{t:tree} (
  pf: BUILDREC (xs, hs, d, t, true)): BUILDREC (hs, hs, d, t, true)

prfun lemma_buildrec_sound {d:int}{xs,hs:ilist}{t:tree} .<>. (
  pf: BUILDREC (xs, xs, d, t, true)): TL (d, t, xs) =
  lemma_buildrec_sound_loop (length_istot (), pf) where {

prfun lemma_buildrec_sound_loop {d:int}{xs,hs:ilist}{t:tree}{n:nat} .<n>. (
  pf_len: LENGTH (xs, n), pf: BUILDREC (xs, xs, d, t, true)): TL (d, t, xs) =
case+ pf of
| BLDRequ () => TLnil ()  // xs = cons (d, nil)
| BLDRsuc {xs,hs,ts,hts,tts,ys:ilist}{..}{t1,t2} (  
  // (xs, xs, d, t, true) = (xs, ys, d, t, true)
  // hs::ts => xs
  // hts::tts => ts
  // hs::hts => ys
  // pf1_bld: BUILDREC (xs, hs, d+1, t1, true)
  // pf2_bld: BUILDREC (ts, hts, d+1, t2, true)
  pf1_bld, pf2_bld, pf_app_x_yz, pf_app_y_z, pf_app_x_y) => let
    prval pf1_bld = lemma_buildrec_part (pf1_bld): BUILDREC (hs, hs, d+1, t1,true)
    prval pf2_bld = lemma_buildrec_part (pf2_bld): BUILDREC (hts, hts, d+1, t2,true)

    prval pf_len_x = lemma_buildrec_true_pos (pf1_bld)
    prval pf_len_yz = length_istot {ts} ()
    prval pf_len' = append_length_lemma (pf_app_x_yz, pf_len_x, pf_len_yz)
    prval () = length_isfun (pf_len, pf_len')

    prval pf_len_y = lemma_buildrec_true_pos (pf2_bld)
    prval pf_len_z = length_istot {tts} ()
    prval pf_len_yz' = append_length_lemma (pf_app_y_z, pf_len_y, pf_len_z)
    prval () = length_isfun (pf_len_yz, pf_len_yz')

    prval pf1_tl = lemma_buildrec_sound_loop (pf_len_x, pf1_bld): TL (d+1, t1, hs)
    prval pf2_tl = lemma_buildrec_sound_loop (pf_len_y, pf2_bld): TL (d+1, t2, hts)
  in
    TLcons (pf1_tl, pf2_tl, pf_app_x_y)
  end

}

(* all that needs to be proved *)
prfun build_sound {d:int}{xs:ilist}{t:tree} .<>. (
  pf: BUILD (xs, d, t, true)): TL (d, t, xs) =
case+ pf of
| BLDsucc (pf_buildrec) => lemma_buildrec_sound {d}{xs,xs}{t} (pf_buildrec)

extern prfun build_complete {d:int}{xs:ilist}{t:tree} (
  pf: TL (d, t, xs)): BUILD (xs, d, t, true)

extern prfun BUILD_isfun {d:int}{xs:ilist}{t1,t2:tree}{b1,b2:bool} (
  pf1: BUILD (xs, d, t1, b1), pf2: BUILD (xs, d, t2, b2)): [b1 == b2] void

(* harness *)
stadef qs1 = cons (1, cons (3, cons (3, cons (2, nil))))
stadef t1 = node (leaf, node (node (leaf, leaf), leaf))

stadef qs2 = cons (1, cons (3, cons (2, cons (2, nil))))

extern prfun harness1 (): BUILD (qs1, 0, t1, true)
extern prfun harness2 (): [t2:tree] BUILD (qs2, 0, t2, false)

(* ******************* *)

(* ****** ****** *)

(* end of [problem4.dats] *)


