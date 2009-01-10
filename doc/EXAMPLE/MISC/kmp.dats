(*
 *
 * An implementation of KMP string search algorithm in ATS
 * 
 *)

// March 2007:
// Author: Hongwei Xi (* hwxi AT CS DOT BU DOT EDU *)

// In this implementation, both memory safety and termination
// of the algorithm are guaranteed with no use of run-time
// checks. Compared to a previous implementation in DML (1998),
// which requires run-time checks to ensure safe array access,
// the progress made during these years in support of dependent
// types for practical programming should be evident.

stadef intsz: int = sizeof (Int)

// extern val intsz: int intsz = "ats_intsz"
val intsz = sizeof<Int>

extern fun ptr_get_t
  {i:int} {l:addr} (pf: !int i @ l | p: ptr l):<> int i
  = "ats_ptr_get_t"

extern fun ptr_set_t {i:int} {l:addr} 
  (pf: !(int i)? @ l >> int i @ l | p: ptr l, i: int i):<> void
  = "ats_ptr_set_t"
  
extern fun array_int_ptr_make {n:nat}
  (n: int n):<> [l:addr] (free_ngc_v l, array_v (Int?, n, l) | ptr l) 
  = "ats_array_int_ptr_make"

extern fun array_int_ptr_free {n:nat} {l:addr}
  (_: free_ngc_v l, _: array_v (Int?, n, l) | p: ptr l):<> void
  = "ats_array_int_ptr_free"

%{^

ats_int_type ats_intsz = sizeof(ats_int_type) ;

static inline
ats_int_type ats_ptr_get_t(ats_ptr_type arg) { 
  return *((ats_int_type *)arg) ; 
}

static inline
ats_void_type ats_ptr_set_t(ats_ptr_type arg1, ats_int_type arg2) {
  *((ats_int_type *)arg1) = arg2;
}

static inline
ats_ptr_type ats_array_int_ptr_make(ats_int_type n) {
  return ats_calloc_ngc(n, sizeof(int)) ;
}

static inline
ats_void_type ats_array_int_ptr_free (ats_ptr_type A) {
  ats_free_ngc(A) ;
}

%}

//

dataview kmp_v (l:addr, int) =
  | kmp_v_none (l, 0)
  | {n:nat} {ofs:int} kmp_v_more (l, n+1) of
      (MUL (n+1, intsz, ofs), kmp_v (l, n), natLte n @ (l + ofs))

//

prfun kmp_v_takeout
   {n,i:int | 0 < i; i <= n} {l:addr} {ofs:int} .<n>.
   (pf0_mul: MUL (i, intsz, ofs), pf0_kmp: kmp_v (l, n))
  : [i1:nat | i1 < i] (
    int i1 @ l + ofs, int i1 @ l + ofs -<lin> kmp_v (l, n)
  ) = let
  prval kmp_v_more (pf_mul, pf_kmp, pf_elt) = pf0_kmp
in
  sif i == n then let
    val () = mul_isfun (pf0_mul, pf_mul)
  in
    #[.. | (pf_elt, llam pf_elt => kmp_v_more (pf_mul, pf_kmp, pf_elt))]
  end else let
    prval (pf1_elt, pf1_rest) = kmp_v_takeout {n-1,i} (pf0_mul, pf_kmp)
  in
    #[.. | (pf1_elt, llam pf1_elt => kmp_v_more (pf_mul, pf1_rest pf1_elt, pf_elt))]
  end // end of [sif]
end // end of [kmp_v_takeout]

//

fn kmp_sub {n,i:int | 0 < i; i <= n} {l:addr}
   (pf_kmp: !kmp_v (l, n) | tbl: ptr l, i: int i)
  :<> [i1:nat | i1 < i] int (i1) =
  let
     val (pf_mul | ofs) = i imul2 intsz
     prval (pf_elt, pf_rest) = kmp_v_takeout (pf_mul, pf_kmp)
     val i1 = ptr_get_t (pf_elt | tbl + ofs)
  in
     pf_kmp := pf_rest pf_elt; i1
  end

//

extern fun string1_get_char_at {n:nat}
  (s: string n, i: natLt n):<> [c:char | c <> NUL] char c
  = "atspre_string_get_char_at"

macdef get (s, i) = string1_get_char_at (,(s), ,(i))

//

fun kmp_table_make_aux
   {i,j,n:int | 0 <= j; j+1 < i; i <= n} {l:addr} {ofs:int} .<n-i,j>.
   (pf_mul: MUL (i, intsz, ofs),
    pf_kmp: kmp_v (l, i-1),
    pf_arr: array_v (Int?, n-i, l+ofs) |
    w: string n, tbl: ptr l, n:int n, i: int i, j: int j, tbl_ofs: ptr(l+ofs))
  :<> (kmp_v (l, n-1) | void) = begin
  if i < n then
    if get (w, i-1) = get (w, j) then let
       prval (pf_elt, pf_arr) = array_v_uncons {Int?} pf_arr
       val () = ptr_set_t (pf_elt | tbl_ofs, j+1)
       prval pf_kmp = kmp_v_more (pf_mul, pf_kmp, pf_elt)
       prval pf_mul = mul_add_const {1} (pf_mul)
    in
       kmp_table_make_aux
         (pf_mul, pf_kmp, pf_arr | w, tbl, n, i+1, j+1, tbl_ofs+intsz)
    end else if j > 0 then
      kmp_table_make_aux
        (pf_mul, pf_kmp, pf_arr | w, tbl, n, i, kmp_sub (pf_kmp | tbl, j), tbl_ofs)
    else let
      prval (pf_elt, pf_arr) = array_v_uncons {Int?} pf_arr
      val () = ptr_set_t (pf_elt | tbl_ofs, 0)
      prval pf_kmp = kmp_v_more (pf_mul, pf_kmp, pf_elt)
      prval pf_mul = mul_add_const {1} (pf_mul)
    in
      kmp_table_make_aux
        (pf_mul, pf_kmp, pf_arr | w, tbl, n, i+1, 0, tbl_ofs+intsz)
    end
  else let
    prval () = array_v_unnil pf_arr in (pf_kmp | ())
  end // end of [if]
end // end of [kmp_table_make_aux]

//

fn kmp_table_make {n:int | n >= 1} (w: string n, n: int n)
  :<> [l:addr] (free_ngc_v (l+intsz), kmp_v (l, n-1) | ptr l) = let
  val n = string1_length w
  val [l:addr] (pf_ngc, pf_arr | p_arr) = array_int_ptr_make (n-1)
  val tbl = p_arr-intsz
  prval pf_kmp = kmp_v_none {l-intsz}
in
  if n > 1 then let
    prval (pf_elt, pf_arr) = array_v_uncons {Int?} (pf_arr)
    val () = ptr_set_t (pf_elt | p_arr, 0)
    prval pf1_mul = mul_make_const {1,intsz} ()
    prval pf2_mul = mul_make_const {2,intsz} ()
    prval pf_kmp = kmp_v_more {l-intsz} (pf1_mul, pf_kmp, pf_elt)
    val (pf_kmp | ()) = kmp_table_make_aux
      (pf2_mul, pf_kmp, pf_arr | w, tbl, n, 2, 0, p_arr+intsz)
  in
    (pf_ngc, pf_kmp | tbl)
  end else let
    prval () = array_v_unnil{Int?} (pf_arr)
  in
    (pf_ngc, pf_kmp | tbl)
  end
end // end of [kmp_table_make]

//

prfun array_v_of_kmp_v {n:nat} {l:addr} .<n>.
  (pf_kmp: kmp_v (l, n)): array_v (Int?, n, l+intsz) = begin
  sif n == 0 then
    let prval kmp_v_none () = pf_kmp in array_v_nil {Int?} () end
  else let
    prval kmp_v_more (pf_mul, pf_kmp, pf_elt) = pf_kmp
    prval pf1_mul = mul_add_const {~1} (pf_mul)
    prval pf_arr = array_v_of_kmp_v pf_kmp
  in
    array_v_extend {Int?} (pf1_mul, pf_arr, pf_elt)
  end
end // end of [array_v_of_kmp_v]

fn kmp_table_free {n:nat} {l:addr}
  (pf_ngc: free_ngc_v (l+intsz), pf_kmp: kmp_v (l, n) | p: ptr l)
  :<> void = let
  prval pf_arr = array_v_of_kmp_v pf_kmp
in
  array_int_ptr_free (pf_ngc, pf_arr | p+intsz)
end // end of [kmp_table_free]

//

fn kmp_search {ns:nat; nw:int | nw >= 1}
   (s: string ns, w: string nw):<> intBtw (~1, ns) = let
  val ns = string1_length s
  val nw = string1_length w
  val [l:addr] (pf_ngc, pf | tbl) = kmp_table_make (w, nw)
  fun aux {m,i:nat | m+i <= ns; i <= nw} .<ns-m-i, i>.
    (pf: !kmp_v (l, nw-1) | m: int m, i: int i):<cloptr> intBtw (~1, ns) =
    if i = nw then m else begin
      if m+i < ns then
        if get (w, i) = get (s, m+i) then aux (pf | m, i+1) else begin
          if i > 0 then begin
            let val i1 = kmp_sub (pf | tbl, i) in aux (pf | m+i-i1, i1) end
          end else begin
            aux (pf | m+1, 0)
          end
        end // end of [if]
      else ~1
    end // end of [if]
  val ans = aux (pf | 0, 0)
in
  kmp_table_free (pf_ngc, pf | tbl); ans
end // end of [kmp_search]

// some tests

implement main (argc, argv) = begin
  print "kmp_search(\"abcdefggfedcbabcdefg\", \"fggf\") = ";
  print (kmp_search("abcdefggfedcbabcdefg", "fggf"));
  print_newline ();

  print "kmp_search(\"abcdefggfedcbabcdefg\", \"cbabc\") = ";
  print (kmp_search("abcdefggfedcbabcdefg", "cbabc"));
  print_newline ();

  print "kmp_search(\"abcdefggfedcbabcdefg\", \"baba\") = ";
  print (kmp_search("abcdefggfedcbabcdefg", "baba"));
  print_newline ();

  print "kmp_search(\"abcdefggfedcbabadefg\", \"baba\") = ";
  print (kmp_search("abcdefggfedcbabadefg", "baba"));
  print_newline ();
end

(* ****** ****** *)

(* end of [kmp.dats] *)

////

// An (untested) implementation in C

(*

#include <stdlib.h>

int main()
{
  unsigned int Fail[1024];
  unsigned int M, K, R, i;
  const char* P = "AAAABAABACA";

  M = strlen(P);
  K = 1;

  Fail[K] = 0;

  while (K <= M) {
    R = Fail[K];

    while ((R > 0) && (P[R-1] != P[K-1]))
      R = Fail[R];

    Fail[K+1] = R+1;
    K++;
  }

  /*
  K = 1;
  while (K <= M) {
    R = Fail[K];

    if (P[K-1] == P[R-1])
      Fail[K] = Fail[R];

    K++;
  }
  */

  for (i = 1; i <= M+1; i++)
    printf("Fail[%d] = %d\n", i, Fail[i]);

  return 0;
}

*)
