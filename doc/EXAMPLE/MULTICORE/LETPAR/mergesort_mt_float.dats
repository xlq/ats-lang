%{^

#include "libats/CATS/thunk.cats"

#include "libc/CATS/pthread.cats"
#include "libc/CATS/pthread_locks.cats"

%}

staload "libc/SATS/pthread.sats"
staload "libc/SATS/pthread_locks.sats"

(* ****** ****** *)

dynload "libats/DATS/parallel.dats"

(* ****** ****** *)

#define ARG_MERGESORT_MT_DATS 1

(*

absviewt@ype T
extern fun lte_T_T (x: !T, y: !T):<> bool
extern fun compare_T_T (x: !T, y: !T):<> Sgn

overload compare with compare_T_T
overload <= with lte_T_T

*)

typedef T = double

#include "mergesort_mt.dats"

(* ****** ****** *)

staload Rand = "libc/SATS/random.sats"
staload Time = "libc/SATS/time.sats"

(* ****** ****** *)

fn array_ptr_print {n:nat} {l:addr}
  (pf_arr: !array_v (T, n, l) | A: ptr l, n: int n): void = let
  fn f (i: natLt n, x: &T):<cloptr1> void = begin
    if i > 0 then print ", "; printf ("%.2f", @(x))
  end
in
  iforeach_array_ptr_tsz_cloptr {T} (f, !A, n, sizeof<T>)
end

(* ****** ****** *)

#define N 100.0

fn random_array_ptr_gen {n:nat} (n: int n):<>
  [l:addr | l <> null] (free_gc_v l, array_v (T, n, l) | ptr l) =
  array_ptr_make_fun_tsz_cloptr {T} (
    n
  , lam (x, i) =<cloptr> x := $effmask_ref ($Rand.drand48 () * N)
  , sizeof<T>
  ) // end of [array_ptr_make_fun_tsz_cloptr]

(* ****** ****** *)

fn usage (cmd: string): void = begin
  prerr ("Usage:\n");
  prerrf ("  single core: %s [integer]\n", @(cmd));
  prerrf ("  multiple core: %s [integer(arg)] [integer(core)]\n", @(cmd));
end

implement main (argc, argv) = begin
  if argc >= 2 then let
    var nthread: int = 0
    val n = int1_of argv.[1] // turning string into integer
    val () = assert (n >= 0)
    val () = if argc >= 3 then (nthread := int_of argv.[2])
    val () = parallel_worker_add_many (nthread)
    val () = printf ("There are now [%i] workers.", @(nthread))
    val () = print_newline ()
    val (pf_gc, pf_arr | A) = random_array_ptr_gen (n)
(*
    val () = array_ptr_print (pf_arr | A, n)
    val () = print_newline ()
*)
    val () = mergesort (pf_arr | A, n)
(*
    val () = array_ptr_print (pf_arr | A, n)
    val () = print_newline ()
*)
  in
    array_ptr_free {T} (pf_gc, pf_arr | A)
  end else begin
    usage argv.[0]; exit (1)
  end
end // end of [main]

(* ****** ****** *)

(* end of [mergesort_mt_float.dats] *)
