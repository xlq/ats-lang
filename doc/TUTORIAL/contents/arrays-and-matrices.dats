//
//
// code for illustration in arrays-and-matrices.html
//
//

%{^

#include "prelude/CATS/array.cats"
#include "prelude/CATS/matrix.cats"

%}

(* ****** ****** *)

staload "prelude/DATS/array.dats"
staload "prelude/DATS/matrix.dats"

(* ****** ****** *)

// persistent arrays

// digits: array (int, 10)
val digits = array $arrsz[int](0, 1, 2, 3, 4, 5, 6, 7, 8, 9)

typedef digit = [i:nat | i < 10] int (i)

// digits: array (digit, 10)
val digits = array $arrsz[digit](0, 1, 2, 3, 4, 5, 6, 7, 8, 9)

val digits = begin
  array_make_fun_tsz_cloptr {digit}
    (10, lam (x, i) =<cloptr> x := i, sizeof<digit>)
end // end of [val]

fn array_square {n:nat}
  (A: array (double, n), sz: int n): void = loop (0) where {
  fun loop {i:nat | i <= n} .<n-i>. (i: int i):<cloptr1> void =
    if i < sz then
      let val x = A[i] in A[i] := x * x; loop (i+1) end
    else ()
} // end of [array_square]

fn array_square {n:nat}
  (A: array (double, n), sz: int n): void = let
  prval pf = unit_v ()
  val () =  iforeach_array_cloptr<double>
    (pf | lam (pf | i, x) =<cloptr,!ref> A[i] := x * x, A, sz)
  prval unit_v () = pf
in
  // empty
end // end of [array_square]

// printing an array

fun{a:t@ype} prarr {n:nat}
  (pr: a -> void, A: array (a, n), sz: int n): void = let
  fun loop {i:nat | i <= n} (n: int n, i: int i):<cloptr1> void =
    if i < n then (if i > 0 then print ", "; pr A[i]; loop (n, i+1))
in
  loop (sz, 0); print_newline ()
end // end of [prarr]

(* ****** ****** *)

// persistent matrices

val mat_10_10 =
  matrix (10, 10) $arrsz[Int](
   0,  1,  2,  3,  4,  5,  6,  7,  8,  9
, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19
, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29
, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39
, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49
, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59
, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69
, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79
, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89
, 90, 91, 92, 93, 94, 99, 96, 97, 98, 99
) // end of [val]

val mat_10_10 = matrix_make_fun_tsz_cloptr {Int}
  (10, 10, lam (x, i, j) =<cloptr> x := 10 * i + j, sizeof<Int>)

// template function for transposing a square matrix

fn{a:t@ype} matrix_transpose {n:nat}
  (A: matrix (a, n, n), n: int n): void = let
  fn get {i,j:nat | i < n; j < n}
   (A: matrix (a, n, n), i: int i, j: int j):<cloref1> a =
   matrix_get_elt_at (A, i, n, j)

  fn set {i,j:nat | i < n; j < n}
   (A: matrix (a, n, n), i: int i, j: int j, x: a):<cloref1> void =
   matrix_set_elt_at (A, i, n, j, x)

  overload [] with get; overload [] with set

  // [fn*] indicates a request for tail-call optimization
  fn* loop1 {i:nat | i <= n} .< n-i+1, 0 >.
    (i: int i):<cloptr1> void = begin
    if i < n then loop2 (i, 0) else ()
  end

  and loop2 {i,j:nat | i < n; j <= i} .< n-i, i-j+1 >.
    (i: int i, j: int j):<cloptr1> void = begin
    if j < i then
      let val x = A[i,j] in A[i,j] := A[j,i]; A[j,i] := x; loop2 (i, j+1) end
    else begin
      loop1 (i+1)
    end
  end // end of [loop2]
in
  loop1 0
end // end of [matrix_transpose]

fn{a:t@ype} matrix_transpose {n:nat}
  (M: matrix (a, n, n), n: int n): void = begin
  iforeach_matrix_cloptr<a> (
    lam (i,j, x) =<cloptr,!ref>
      if i > j then let
        val x = matrix_get_elt_at (M, i, n, j)
      in
        matrix_set_elt_at (M, i, n, j, matrix_get_elt_at (M, j, n, i));
        matrix_set_elt_at (M, j, n, i, x)
      end
  , M, n, n
  ) // end of [iforeach_matrix]
end // end of [matrix_transpose]

// printing a matrix

fn{a:t@ype} prmat {m,n:nat}
  (pr: a -> void, M: matrix (a, m, n), m: int m, n: int n)
  : void = let
  fn* loop1 {i:nat | i <= m} (i: int i):<cloptr1> void =
    if i < m then loop2 (i, 0) else print_newline ()
  and loop2 {i,j:nat | i < m; j <= n}
    (i: int i, j: int j):<cloptr1> void = begin
    if j < n then let
      val x = matrix_get_elt_at (M, i, n, j)
    in
      if (j > 0) then print ", "; pr x; loop2 (i, j+1)
    end else begin
      print_newline (); loop1 (i+1)
    end
  end // end of [loop2]
in
  loop1 0
end // end of [prmat]

(* ****** ****** *)

// a variant implementation of [prarr] based in array iteration

fn{a:t@ype} prarr_ {n:nat}
  (pr: a -> void, A: array (a, n), n: int n): void = let
  var i: int = (0: int)
  typedef env_t = @(a -> void, ptr i)
  var env: env_t; val () = env.0 := pr; val () = env.1 := &i
  viewdef V = (int @ i, env_t @ env)
  fn f (pf: !V | x: a, p_env: !ptr env): void = let
    prval (pf1, pf2) = pf; val p = p_env->1; val i = !p
    val () = (if i > 0 then print ", "; p_env->0 (x); !p := i + 1)
  in
    pf := (pf1, pf2)
  end
  prval pf = (view@ i, view@ env)
in
  foreach_array_main<a> {V} (pf | f, A, n, &env);
  view@ i := pf.0; view@ env := pf.1;
  print_newline ();
end // end of [prarr_]

// a variant implementation of [prmat] based in matrix iteration

fn{a:t@ype} prmat_ {m,n:nat}
  (pr: a -> void, M: matrix (a, m, n), m: int m, n: int n)
  : void = let
  var j: int = (0: int)
  typedef env_t = @(int (n-1), a -> void, ptr j)
  var env: env_t; val () = (env.0 := n-1; env.1 := pr; env.2 := &j)
  viewdef V = (int @ j, env_t @ env)
  fn f (pf: !V | x: a, p_env: !ptr env): void = let
    prval (pf1, pf2) = pf
    val p = p_env->2; val j = !p
  in
    if j > 0 then print ", "; p_env->1 (x); !p := j + 1;
    if j >= p_env->0 then (!p := 0; print_newline ());
    pf := (pf1, pf2)
  end
  prval pf = (view@ j, view@ env)
in
  foreach_matrix_main<a> {V} (pf | f, M, m, n, &env);
  view@ j := pf.0; view@ env := pf.1;
  print_newline ()
end // end of [prmat_]

(* ****** ****** *)

implement main (argc, argv) = let

fn pr1 (x: Int): void = print x
fn pr2 (x: Int): void = printf ("%2i", @(x))

in

// testing prarr
print "printed by [prarr]:\n";
prarr (pr1, digits, 10);
print_newline ();

// testing prarr and prarr_:
print "printed by [prarr_]:\n";
prarr_ (pr1, digits, 10);
print_newline ();

// testing prmat
print "before matrix transposition (printed by [prmat]):\n";
prmat (pr2, mat_10_10, 10, 10);

// testing matrix_transpose
matrix_transpose (mat_10_10, 10);

// testing prmat_
print "after matrix transposition (printed by [prmat_]):\n";
prmat_ (pr2, mat_10_10, 10, 10);

end // end of [main]

(* ****** ****** *)

(* end of [arrays-and-matrices.dats] *)
