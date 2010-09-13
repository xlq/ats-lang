(*
//
// Author: Hongwei Xi (September, 2010)
//
*)

(* ****** ****** *)

staload RAND = "libc/SATS/random.sats"

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array.dats"

(* ****** ****** *)

staload V = "libats/SATS/vector.sats"
stadef VSHELL = $V.VSHELL
stadef VSHELL0 = $V.VSHELL0
stadef VECTOR = $V.VECTOR

(* ****** ****** *)

staload _(*anon*) = "libats/DATS/vector.dats"

(* ****** ****** *)

macdef size1 (x) = size1_of_int1 ,(x)

implement main () = () where {
  #define N 10
  typedef T = double
  var V: VSHELL0 // unintialized
  val () = $V.vector_initialize<double> (V, N)
  val () = loop (V, 0) where {
    fun loop {m,n:int}
      {i:nat | i <= N; n+N <= m+i} .<N-i>. (
        V: &VECTOR (T, m, n) >> VECTOR (T, m, n+N-i), i: size_t i
      ) :<> void =
      if i < N then let
        val () = $V.vector_append (V, (double_of)i) in loop (V, i+1)
      end // end of [if]
    // end of [loop]
  } // end of [val]
//
  var i: natLte (N)
  val () = for*
    (V: VECTOR (T, N, N)) => (i := 0; i < N; i := i+1)
    (printf ("V[%i] = %.1f\n", @(i, $V.vector_get_elt_at (V, (size1)i))))
//
  val () = $V.vector_uninitialize (V)
//
  var V: VSHELL0 // unintialized
  val () = $V.vector_initialize<double> (V, N)
  val () = loop (V, 0) where {
    fun loop {m,n:int}
      {i:nat | i <= N; n+N <= m+i} .<N-i>. (
        V: &VECTOR (T, m, n) >> VECTOR (T, m, n+N-i), i: size_t i
      ) :<> void =
      if i < N then let
        val () = $V.vector_prepend (V, (double_of)i) in loop (V, i+1)
      end // end of [if]
    // end of [loop]
  } // end of [val]
//
  var i: int = 0
  viewdef V = int@i
  val () = $V.vector_foreach_clo<T>
    {V} (view@ i | V, !p_clo) where {
    var !p_clo = @lam (pf: !int@i | x: &T)
      : void =<> $effmask_all (printf ("V[%i] = %.1f\n", @(i,x)); i:=i+1)
  } // end of [val]
//
  val () = $V.vector_uninitialize (V)
//
} // end of [main]

(* ****** ****** *)

(* end of [libats_vector.dats] *)
