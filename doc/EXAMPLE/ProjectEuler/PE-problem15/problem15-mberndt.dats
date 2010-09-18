//
// Author: Matthias Berndt (matthias_berndt AT gmx DOT de)
//   with some minor fixes by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

dataprop PATHS(int, int, int) =
  | {y:nat} PATHSbas1(0, y, 1)
  | {x:nat} PATHSbas2(x, 0, 1)
  | {x,y,z1,z2:nat}
    PATHSind(x+1, y+1, z1+z2) of (PATHS(x, y+1, z1), PATHS(x+1, y, z2))
// end of [PATHS]

datasort ilst = 
  | ilst_nil of () | ilst_cons of (int, ilst)
// end of [ilst]

dataprop LENGTH (ilst, int) =
  | LENGTHnil (ilst_nil, 0)
  | {x:int} {xs:ilst} {n:nat}
    LENGTHcons (ilst_cons (x, xs), n+1) of LENGTH (xs, n)
// end of [LENGTH]

(*
// MB:
// If PATHS_LIST(zs, y) holds, then zs constains numbers z_n, ..., z_2, z_1
// such that PATHS(n, y, z_n), ..., PATHS(2, y, z_2), PATHS(1, y, z_1) hold
*)
dataprop PATHS_LIST(ilst, int (*y*)) = 
  | {y:nat} PATHS_LISTbas(ilst_nil, y)
  | {x,y,z:nat} {zs:ilst}
    PATHS_LISTind(ilst_cons(z, zs), y) of (LENGTH(zs, x), PATHS(x, y, z), PATHS_LIST(zs, y))
// end of [PATHS_LIST]

dataprop SUM (ilst, int) =
  | SUMbas (ilst_nil, 0)
  | {x:int} {xs:ilst} {sum:int} SUMind(ilst_cons(x,xs), x+sum) of SUM(xs, sum)
// end of [SUM]

(* 
// MB:
// PSUMS -- partial sums. 
// let xs = x_n, ..., x_2, x_1. 
// let sums = sum_n, ..., sum_2, sum_1
// If PSUMS(xs, sums) holds, then 
// sum_1 = x_1
// sum_2 = x_1 + x_2
// ...
// sum_n = x_1 + x_2 + ... + x_n
*)
dataprop PSUMS(ilst (*xs*), ilst (*sums*)) = 
  | PSUMSbas(ilst_nil, ilst_nil)
  | {x:int} {xs: ilst} {sum:int} {sums: ilst}
    PSUMSind(ilst_cons(x, xs), ilst_cons(x+sum, sums)) of (PSUMS(xs, sums), SUM (xs, sum))
// end of [PSUMS]

(*
// MB: If PSUMS(xs, sums) holds, then xs and sums have the same length
*)
prfun PSUMS_same_length {xs,sums:ilst} {n:nat} .<xs>.
  (pf1: PSUMS (xs, sums), pf2: LENGTH (xs, n)): LENGTH (sums, n) =
  scase xs of
  | ilst_cons (x, xs1) => let
      prval PSUMSind (pf1, _) = pf1 and LENGTHcons (pf2) = pf2
    in
      LENGTHcons (PSUMS_same_length (pf1, pf2))
    end // end of [ilst_cons]
  | ilst_nil () => let
      prval PSUMSbas () = pf1 and LENGTHnil () = pf2 in LENGTHnil ()
    end // end of [ilst_nil]
// end of [PSUMS_same_length]

(* LENGTH is a total relation *)
prfun LENGTHistot
  {xs:ilst} .<xs>. (): [n:nat] LENGTH (xs, n) =
  scase xs of
  | ilst_cons (x, xs1) => LENGTHcons (LENGTHistot {xs1} ())
  | ilst_nil () => LENGTHnil ()
// end of [LENGTHistot]

(* LENGTH is a functional relation *)
prfun LENGTHisfun {xs:ilst} {n1,n2:int} .<xs>.
  (pf1: LENGTH (xs, n1), pf2: LENGTH (xs, n2)): [n1==n2] void =
  scase xs of
  | ilst_cons (_, xs1) => let
      prval LENGTHcons pf1 = pf1 and LENGTHcons pf2 = pf2
    in
      LENGTHisfun {xs1} (pf1, pf2)
    end // end of [ilst_cons]
  | ilst_nil () => let
      prval LENGTHnil () = pf1 and LENGTHnil () = pf2
    in
      // nothing
    end // end of[ ilst_nil]
// end of [LENGTHisfun]

(* ****** ****** *)

//
// HX: A representation good enough for 64-bit unsigned integers
//
abst@ype ullint1 (i: int) = ullint
//
symintr ullint1
extern castfn ullint1_int {i:nat} (x: int i):<> ullint1 i
overload ullint1 with ullint1_int
//
extern fun print_ullint1
  {i:nat} (x: ullint1 i): void = "atspre_print_ullint"
extern fun add_ullint1_ullint1
  {z1,z2:nat} (z1: ullint1 z1, z2: ullint1 z2):<> ullint1 (z1+z2)
  = "atspre_add_ullint_ullint"
overload + with add_ullint1_ullint1

(* ****** ****** *)

datatype ilist (ilst) =
  | ilist_nil (ilst_nil) of ()
  | {x:nat} {xs:ilst} ilist_cons (ilst_cons (x, xs)) of (ullint1 x, ilist (xs))
// end of [ilist]

#define nil ilist_nil
#define cons ilist_cons
#define :: ilist_cons

(* ****** ****** *)

(*
// MB: calculate the list of partial sums for any given list.
*)
fun psums {xs:ilst} .<xs>.
  (xs: ilist (xs)):<> [sums: ilst] (PSUMS(xs, sums) | ilist sums) =
  case+ xs of 
  | nil() => (PSUMSbas() | nil())
  | cons (x, nil()) => (PSUMSind(PSUMSbas(), SUMbas()) | x::nil())
  | cons {x} {xs1} (x, xs1 as cons _) => let
      prval pflen_xs1 = LENGTHistot {xs1} ()
      val+ (pf | ys1) = psums (xs1)
      prval LENGTHcons _ = pflen_xs1
      prval pflen_ys1 = PSUMS_same_length (pf, pflen_xs1)
      prval LENGTHcons _ = pflen_ys1
      val+ y1 :: ys2 = ys1
      prval PSUMSind (pf1, pf2) = pf
    in
      (PSUMSind(pf, SUMind(pf2)) | (x+y1)::ys1)
    end
// end of [psums]

(* ****** ****** *)

extern
prfun PATHS_LIST_PSUMS_lemma1 {xs1,xs2:ilst}
  {k:nat} (pf1: PATHS_LIST(xs1, k), pf2: PSUMS(xs1, xs2)): PATHS_LIST(xs2, k+1)`

fun paths_list {len,y:nat} .<len+y>.
  (len: int len, y: int y)
  :<> [zs:ilst] ((PATHS_LIST(zs, y), LENGTH(zs, len)) | ilist zs) = 
  case+ y of
  | 0 => (case+ len of
     | 0 => ((PATHS_LISTbas(), LENGTHnil()) | nil())
     | len =>> let
         val+ ((pf1, pf2) | xs) = paths_list (len-1, 0)
       in
         ((PATHS_LISTind(pf2, PATHSbas2(), pf1),LENGTHcons(pf2)) | (ullint1)1::xs)
       end
    ) // end of [0]
  | y =>> let
      val+ ((pf_paths_list, pf_len_xs) | xs) = paths_list(len, y-1)
      val+ (pf_psums | sums) = psums (xs)
      prval pf_len_sums = PSUMS_same_length(pf_psums, pf_len_xs)
      prval pfres = (PATHS_LIST_PSUMS_lemma1(pf_paths_list, pf_psums), PSUMS_same_length(pf_psums, pf_len_xs))
    in
      (pfres | sums)
    end // end of [y > 0]
// end of [paths_list]

fun paths{x,y: nat} .<>.
  (x: int x, y: int y):<> [z: nat] (PATHS(x, y, z) | ullint1 z) =
  case+ y of 
  | 0 => (PATHSbas2() | (ullint1)1)
  | y =>> let
      val ((pf_paths_list, pf_len) | zs) = paths_list(x+1, y) 
      prval LENGTHcons pf1_len = pf_len (* needed for exhaustiveness checks *)
      prval PATHS_LISTind(pf1, pf2, pf3) = pf_paths_list
      prval () = LENGTHisfun (pf1_len, pf1)
      val z :: _ = zs
    in
      (pf2 | z)
    end // end of [y > 0]
// end of [paths]

implement main () = let 
  val (_ | ans) = paths(20, 20)
//
extern castfn ullint_of_ullint1 {i:nat} (x: ullint1 i):<> ullint
//
  val () = assert_errmsg (ullint_of_ullint1(ans) = 137846528820ULL, #LOCATION)
in
  print ("The answer = "); print_ullint1 ans; print_newline ()
end // end of [main]

(* ****** ****** *)

(* end of [problem15-mberndt.dats] *)
