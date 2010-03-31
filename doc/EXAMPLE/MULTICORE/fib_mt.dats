//
// fib_mt.dats: computing Fibonacci numbers
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: March, 2010
//

(* ****** ****** *)

staload "libc/SATS/pthread.sats"

(* ****** ****** *)

staload "libats/SATS/parworkshop.sats"
staload _ = "libats/DATS/parworkshop.dats"

(* ****** ****** *)

macdef int64 = int64_of_int

fun fib
  (n: int, sum: &int64): void =
  if n >= 2 then let
    val () = fib (n-1, sum); val () = fib (n-2, sum)
  in
    // nothing
  end else
    sum := sum + (int64)n
  // end of [if
// end of [fib]

(* ****** ****** *)

dataviewtype ans =
  | D of (ans, ans) | S of int64

fun finalize (t: ans): int64 =
  case+ t of
  | ~D (t1, t2) => finalize t1 + finalize t2
  | ~S sum => sum
// end of [finalize]

(* ****** ****** *)

viewtypedef work = () -<lincloptr1> void
viewtypedef WSptr (l:addr) = WORKSHOPptr (work, l)

(* ****** ****** *)

fun fwork {l:addr}
  (ws: !WSptr l, wk: &work >> work?): int = let
  val wk = wk
  val pfun = __cast (wk) where {
    extern castfn __cast
      (wk: !work >> opt (work, l > null)): #[l:addr] ptr l
  } // end of [val]
in
  if pfun > null then let
    prval () = opt_unsome {work} (wk)
    val () = wk ()
    val () = cloptr_free (wk)
  in
    1 // the worker is to continue
  end else let
    val i = intptr_of_ptr (pfun)
    prval () = opt_unnone {work} (wk)
    prval () = cleanup_top {work} (wk)
  in
    int_of_intptr (i) // the worker is to pause or quit
  end // end of [if]
end // end of [fwork]

(* ****** ****** *)

fun fib_split {l:addr}
  (N: int, ws: !WSptr l, n: int): ans = let
in
  if n > N then let
    val ans1 = fib_split (N, ws, n-1)
    and ans2 = fib_split (N, ws, n-2)
  in
    D (ans1, ans2)
  end else let
    val res = S (?)
    val S (!p) = res
    val () = !p := (int64)0
    extern prfun __ref
      {l:addr} (pf: !int64 @ l): int64 @ l
    prval pf = __ref (view@ !p)
    extern prfun __unref {l:addr} (pf: int64 @ l): void
    val f = lam (): void =<lincloptr1>
      let val () = fib (n, !p); prval () =__unref (pf) in (*empty*) end
    // val () = f ()
    val () = workshop_insert_work (ws, f)
  in
    fold@ res; res
  end // end of [val]
end // end of [fib_split]

(* ****** ****** *)

dynload "libats/DATS/parworkshop.dats"

(* ****** ****** *)

#define QSZ 1024
#define NWORKER 1

implement
main (argc, argv) = let
  val () = assert_errmsg_bool1
    (argc >= 2, "exit: wrong command format!\n")
  val n = int_of argv.[1]
  val N = n - 16
  val ws = workshop_make<work> (QSZ, fwork)
  val nworker =
    (if (argc >= 3) then int_of argv.[2] else NWORKER): int
  val nworker = int1_of_int (nworker)
  val () = assert_errmsg (nworker > 0, #LOCATION)
  val _err = workshop_add_nworker (ws, nworker)
  val () = assert_errmsg (_err = 0, #LOCATION)
  val t = fib_split (N, ws, n)
  val () = (print "spliting is done"; print_newline ())
  var i: Nat = 0
  val () = while (i < nworker) let
    val _0 = $extval (work, "(void*)0")
    val () = workshop_insert_work (ws, _0) in i := i + 1
  end // end of [val]
  val () = workshop_wait_worker_paused (ws)
  val sum = finalize (t)
  val () = while (i < nworker) let
    val _1 = $extval (work, "(void*)-1")
    val () = workshop_insert_work (ws, _1) in i := i + 1
  end // end of [val]
  val ws = __cast (ws) where {
    extern castfn __cast {l:addr} (_: WSptr l):<> ptr l
  } // end of [val]
in
  print "sum = "; print sum; print_newline ()
end // end of [main]

(* ****** ****** *)

(* end of [partial-sums_mt.dats] *)
