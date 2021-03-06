(*
** The Computer Language Benchmarks Game
** http://shootout.alioth.debian.org/
**
** based on code by Hongwei Xi, Miroslav Rubanets, and Oleg Mazurov
** contributed by Julian Beaumont
**
** compilation command:
**   atscc -fomit-frame-pointer -O3 fannkuch-redux.dats -o fannkuch-redux
*)

(* ****** ****** *)

staload _ = "prelude/DATS/pointer.dats"

(* ****** ****** *)

%{^
//
// HX: this is the best choice on my machine
//
typedef ats_uint_type ats_ussi_type ;
%}
abst@ype ussiLt (n: int) = $extype "ats_ussi_type"

extern castfn ussiLt_of {n : nat | n <= 256} (x : sizeLt  n) :<> ussiLt n
extern castfn sizeLt_of  {n : nat | n <= 256} (x : ussiLt n) :<> sizeLt n

(* ****** ****** *)

viewtypedef iarray (n : int, l : addr)
  = [0 < n && n <= 256] @( array_v (ussiLt n, n, l) | ptr l )

fn array_get {n : nat} {l : addr} {i : nat | i < n}
  (xs : ! iarray (n, l), i : size_t i) :<> sizeLt n = let
  prval pf = xs.0
  val p = xs.1
  val result = p->[i]
  prval () = xs.0 := pf
in sizeLt_of {n} (result) end

fn array_set {n : nat} {l : addr} {i : nat | i < n}
  (xs : ! iarray (n, l), i : size_t i, x : sizeLt n) :<> void = let
  prval pf = xs.0
  val p = xs.1
  val () = p->[i] := (ussiLt_of)x
  prval () = xs.0 := pf
in () end

overload [] with array_get
overload [] with array_set

(* ****** ****** *)

%{^
ATSinline()
ats_void_type array_copy
 (ats_ptr_type src, ats_ptr_type dst, ats_size_type n) {
  memcpy (dst, src, n*sizeof(ats_ussi_type));
}
%}

extern fun array_copy {n : nat} {s, d : addr}
    ( src : ! iarray (n, s), dst : ! iarray (n, d), n : size_t n
    ) :<> void = "array_copy"

(* ****** ****** *)

fn array_fprint {n : nat} {l : addr}
  ( out : FILEref, xs : ! iarray (n, l), n : size_t n ) : void = let
  var i : sizeLte n = size1_of_int1 0
  val () = while (i < n) (fprint_size (out, xs[i]); i := i + 1)
  val () = fprint_char (out, '\n')
in end

fn array_print {n : nat} {l : addr}
  ( xs : ! iarray (n, l), n : size_t n ) : void = begin
  array_fprint (stdout_ref, xs, n)
end

(* ****** ****** *)

fun array_init {n : nat} {l : addr} {i : nat | i <= n} .< n - i >.
        (xs : ! iarray (n, l), n : size_t n, i : size_t i) :<> void =
    if i < n then (xs[i] := i ; array_init (xs, n, i + 1))

fun array_shift {n, i, j : nat | i <= j ; j < n} {l : addr} .< j - i >.
        (xs : ! iarray (n, l), i : size_t i, j : size_t j) :<> void =
    if i < j then (xs[i] := xs[i + 1] ; array_shift (xs, i + 1, j))

fn array_rotate {n : nat} {l : addr}
        (xs : ! iarray (n, l), i : sizeLt n) :<> void = let
    val x0 = xs[size1_of_int1 0]
    val () = array_shift (xs, 0, i)
    val () = xs[i] := x0
in () end

fun array_reverse {n : nat} {x : addr} 
            {l, u : nat | l - 1 <= u ; u < n} .< u - l + 1 >.
        (xs : ! iarray (n, x), l : size_t l, u : size_t u) :<> void = begin
    if l < u then let
        val xl = xs[l]
        val () = xs[l] := xs[u]
        val () = xs[u] := xl
        val () = array_reverse (xs, l + 1, u - 1)
    in () end
end

fun array_next_permutation {n : nat} {c, p : addr} 
            {i : nat | i < n} .< n - i >.
        ( cs : ! iarray (n, c), ps : ! iarray (n, p)
        , n : size_t n, i : size_t i
        ) :<> sizeLte n = let
    val () = array_rotate (ps, i)
    val ci = cs[i] in
    if ci > 0 then (cs[i] := ci - 1 ; i) else let
        val () = cs[i] := i in
        if i + 1 >= n then i + 1 else
            array_next_permutation (cs, ps, n, i + 1)
    end
end

(* ****** ****** *)

typedef result =
    @{ maxFlips = int
     , checksum = int
     }

fun fannkuch {n : nat | n >= 2} {c, p, s : addr}
        ( cs : ! iarray (n, c), ps : ! iarray (n, p), ss : ! iarray (n, s)
        , n : size_t n, count : int, result : &result
        ) : void = let
    val () =
        if array_get (ps, 0) = 0 then () else let
            var flips : int = 0
            val () = array_copy (ps, ss, n)
            var s0 : sizeLt n = ss[size1_of_int1 0]
            val () = while (s0 > 0) let
                val () = flips := flips + 1
                val () = array_reverse (ss, 0, s0)
                val () = s0 := ss[size1_of_int1 0]
            in () end
            val () = result.maxFlips :=
                (if result.maxFlips < flips
                    then flips else result.maxFlips)
            val () = result.checksum := result.checksum +
                (if count mod 2 = 0 then flips else ~flips)
        in () end
    val i = array_next_permutation (cs, ps, n, 1)
in
    if i < n then
        fannkuch (cs, ps, ss, n, count + 1, result)
end

(* ****** ****** *)

implement main (argc, argv) = let
    val () = assert (argc >= 2)
    val [n : int] n = int1_of argv.[1]
    val () = assert (1 < n && n <= 256)
    val n = size1_of_int1 n
    val z = ussiLt_of (size1_of_int1 (0))
    var !cs with pcs = @[ussiLt n][n](z)
    var !ps with pps = @[ussiLt n][n](z)
    var !ss with pss = @[ussiLt n][n](z)
    val acs = @(pcs | cs)
    val aps = @(pps | ps)
    val ass = @(pss | ss)
    val () = array_init (acs, n, 0)
    val () = array_init (aps, n, 0)
    var ans : result = @{ maxFlips = 0, checksum = 0 }
    val () = fannkuch (acs, aps, ass, n, 0, ans)
    prval () = pcs := acs.0
    prval () = pps := aps.0
    prval () = pss := ass.0
in
    printf ("%i\n", @(ans.checksum));
    printf ("Pfannkuchen(%i) = %i\n", @(int1_of_size1 (n), ans.maxFlips))
end

(* ****** ****** *)

(* end of [fannkuch2-redux.dats] *)
