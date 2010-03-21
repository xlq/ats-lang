(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -O3 k-nucleotide.dats -o k-nucleotide -D_ATS_GCATS
*)

(* ****** ****** *)

staload "libc/SATS/stdio.sats"
staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

%{^

typedef ats_ptr_type ats_string_type ;
typedef struct { char *ptr ; int len ; } ptr_len_struct ;
typedef ptr_len_struct symbol_t ;

%}

(* ****** ****** *)

abstype dna_t // boxed type
abst@ype symbol_t = $extype "symbol_t"

(* ****** ****** *)

extern fun print_symbol (sym: symbol_t): void = "print_symbol"

extern fun symbol_make_dnaseg
  (dna: dna_t, off: int, len: int): symbol_t = "symbol_make_dnaseg"
extern fun symbol_make_strint
  {n:nat} (str: string n, n: int n): symbol_t = "symbol_make_strint"

extern fun cmp_symbol_symbol
  (sym1: symbol_t, sym2: symbol_t):<> Sgn = "cmp_symbol_symbol"

%{$

ats_void_type print_symbol (symbol_t sym) {
  char *ptr ; int len ;
  ptr = sym.ptr ; len = sym.len ;
  while (len > 0) { fputc (*ptr, stdout) ; --len ; ++ptr ; }
  return ;
} /* print_symbol */

symbol_t symbol_make_strint (ats_ptr_type str, ats_int_type len) {
  symbol_t sym ;
  sym.ptr = (char*)str ; sym.len = len ;
  return sym ;
}

symbol_t symbol_make_dnaseg
  (ats_ptr_type dna, ats_int_type off, ats_int_type len) {
  symbol_t sym ;
  sym.ptr = ((char*)dna)+off ; sym.len = len ;
  return sym ;
}

ats_bool_type cmp_symbol_symbol (symbol_t sym1, symbol_t sym2) {
  int len1, len2, len, ans ;
  len1 = sym1.len ; len2 = sym2.len ;
  len = (len1 <= len2 ? len1 : len2) ;
  ans = strncmp(sym1.ptr, sym2.ptr, len) ;
  if (!ans) {
    if (len < len1) return  1 ;
    if (len < len2) return -1 ;
    return 0 ;
  }
  return ans ;
}

%}

(* ****** ****** *)

// a linear datatype
dataviewtype frqlst = FRQLSTnil | FRQLSTcons of (symbol_t, float, frqlst)

fun frqlst_sort (frqs: frqlst): frqlst = let
  fun ins (sym: symbol_t, f: float, frqs: frqlst): frqlst =
    case+ frqs of
    | FRQLSTcons (sym1, f1, !frqs1) =>
        if f >= f1 then begin
          fold@ frqs; FRQLSTcons (sym, f, frqs)
        end else begin
          !frqs1 := ins (sym, f, !frqs1); fold@ frqs; frqs
        end // end of [if]
    | FRQLSTnil () => begin
        fold@ frqs; FRQLSTcons (sym, f, frqs)
      end
in
  case+ frqs of
  | ~FRQLSTcons (sym, f, frqs) => ins (sym, f, frqlst_sort frqs)
  | ~FRQLSTnil () => FRQLSTnil ()
end // end of [frqlst_sort]    

fun print_free_frqlst (kfs: frqlst): void = case+ kfs of
  | ~FRQLSTcons (k, f, kfs) => begin
      print_symbol k; printf (" %.3f\n", @(double_of f)); print_free_frqlst kfs
    end // end of [FRQLSTcons]
  | ~FRQLSTnil () => ()
// end of [print_free_frqlst]

(* ****** ****** *)

staload MS = "funmset_avltree.dats"

(* ****** ****** *)

fn cmp_symbol_symbol_cloref
  (sym1: symbol_t, sym2: symbol_t):<cloref> Sgn =
  cmp_symbol_symbol (sym1, sym2)

(* ****** ****** *)

fn dna_count {n,k:nat | k <= n}
  (dna: dna_t, n: int n, k: int k): $MS.mset_t symbol_t = let
  val ms = $MS.funmset_empty {symbol_t} ()
  val nk = n - k
  fun loop {i:nat}
    (ms: $MS.mset_t symbol_t, i: int i)
    :<cloref1> $MS.mset_t symbol_t =
    if i <= nk then let
      val sym = symbol_make_dnaseg (dna, i, k)
      val ms = $MS.funmset_insert (ms, sym, cmp_symbol_symbol_cloref)
    in
      loop (ms, i+1)
    end else begin
      ms // return value
    end // end of [if]
in
  loop (ms, 0)
end // end of [dna_count]

(* ****** ****** *)

fn write_frequencies {n,k:nat | k <= n}
  (dna: dna_t, n: int n, k: int k): void = let
  val ms = dna_count (dna, n, k)
  val total = $MS.funmset_size (ms)
  val ftotal = float_of total
  var frqs: frqlst = FRQLSTnil (); viewdef V2 = frqlst @ frqs
  fn f2 (pf: !V2 | k: symbol_t, cnt: int):<cloref1> void = let
    val fval = 100 * (float_of cnt) / ftotal in frqs := FRQLSTcons (k, fval, frqs)
  end // end of [f2]
  val () = $MS.funmset_foreach_cloref {V2} (view@ frqs | ms, f2)
in
  print_free_frqlst (frqlst_sort frqs)
end // end of [write_frequencies]

(* ****** ****** *)

fn write_count {n,k:nat}
  (dna: dna_t, n: int n, seq: string k): void = let
  val k = length seq; val () = assert (k <= n)
  val ms = dna_count (dna, n, k)
  val sym = symbol_make_strint (seq, k)
  val cnt = begin
    $MS.funmset_member<symbol_t> (ms, sym, cmp_symbol_symbol_cloref)
  end // end of [val]
in
  printf ("%d\t%s\n", @(cnt, seq))
end // end of [write_count]

(* ****** ****** *)

typedef string_int = [n:nat] (string n, int n)

extern fun getline (): string
extern fun getrest (): string_int

dataviewtype charlst (int) =
  | charlst_nil (0)
  | {n:nat} charlst_cons (n+1) of (char, charlst n)

#define nil charlst_nil
#define cons charlst_cons
#define :: charlst_cons

extern fun charlst_is_nil {n:nat} (cs: &charlst n): bool (n == 0) =
  "charlst_is_nil"

implement charlst_is_nil (cs) = case+ cs of
  | nil () => (fold@ cs; true) | cons (c, !cs_r) => (fold@ cs; false)

extern fun
charlst_uncons {n:pos} (cs: &charlst n >> charlst (n-1)): char =
  "charlst_uncons"

implement charlst_uncons (cs) =
  let val ~(c :: cs_r) = cs in cs := cs_r; c end
// end of [charlst_uncons]

extern fun
string_make_charlst_int {n:nat} (cs: charlst n, n: int n): string n =
  "string_make_charlst_int"

#define i2c char_of_int

implement getline () = let
  fun loop {n:nat} (cs: charlst n, n: int n): string =
    let val i = getchar () in
      if i >= 0 then let
        val c = i2c i
      in
        if c <> '\n' then loop (charlst_cons (c, cs), n+1)
        else string_make_charlst_int (cs, n)
      end else begin
        string_make_charlst_int (cs, n)
      end
   end // end of [loop]
in
  loop (charlst_nil (), 0)
end // end of [getline]

implement getrest () = loop (charlst_nil (), 0) where {
  fun loop {n:nat} (cs: charlst n, n: int n): string_int =
    let val i = getchar () in
      if i >= 0 then let
        val c = i2c i
      in
        if c <> '\n' then
          loop (charlst_cons (char_toupper c, cs), n+1)
        else loop (cs, n)
      end else begin
        @(string_make_charlst_int (cs, n), n)
      end
    end // end of [let]
} // end of [getrest]

(* ****** ****** *)

extern fun dna_of_string (s: string): dna_t = "dna_of_string"
extern fun is_three (s: string): bool = "is_three"

%{$

ats_ptr_type dna_of_string (ats_string_type s) { return s ; }

ats_bool_type is_three (ats_ptr_type s0) {
  char *s = (char*) s0 ;

  if (*s != '>') return ats_false_bool ; ++s ;
  if (*s != 'T') return ats_false_bool ; ++s ;
  if (*s != 'H') return ats_false_bool ; ++s ;
  if (*s != 'R') return ats_false_bool ; ++s ;
  if (*s != 'E') return ats_false_bool ; ++s ;
  if (*s != 'E') return ats_false_bool ;
  return ats_true_bool ;
}

%}

implement main (argc, argv) = let

fun dna_three_get (): string_int = let
  val s = getline ()
in
  if s <> "" then
    if is_three (s) then getrest () else dna_three_get ()
  else begin
    exit_errmsg {string_int} (1, "[dna_three_get] failed.\n")
  end // end of [if]
end // end of [dna_three_get]

val () = gc_chunk_count_limit_max_set (~1) // no max

val (dna_three, n) = dna_three_get ()
val dna = dna_of_string dna_three
val () = assert (n >= 2)

in

write_frequencies (dna, n, 1) ; print_newline () ;
write_frequencies (dna, n, 2) ; print_newline () ;

write_count (dna, n, "GGT") ;
write_count (dna, n, "GGTA") ;
write_count (dna, n, "GGTATT") ;
write_count (dna, n, "GGTATTTTAATT") ;
write_count (dna, n, "GGTATTTTAATTTATAGT") ;

end // end of [main]

(* ****** ****** *)

%{$

ats_ptr_type
string_make_charlst_int (ats_ptr_type cs, const ats_int_type n) {
  char *s;
  s = ats_malloc_gc(n+1) ; s += n ; *s = '\000' ;
  while (!charlst_is_nil(&cs)) { *--s = charlst_uncons(&cs) ; }
  return s ;
}

%}

(* ****** ****** *)

(* end of [k-nucleotide1.dats] *)
