//
// randcompec_mt.dats: computing the Euler's constant via randomization
//
// Author: Chris Double (chris DOT double AT double DOT co DOT nz)
// with minor tweaking by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload "libc/SATS/random.sats"
staload "libc/SATS/unistd.sats"
staload "libats/SATS/parworkshop.sats"
staload "libats/DATS/parworkshop.dats"
staload "prelude/DATS/array.dats"

(* ****** ****** *)

#define ITER 100000000
#define NCPU 2

fn random_double (buf: &drand48_data): double = let
  var r: double
  val _ = drand48_r(buf, r)
in
  r
end

fn attempts (buf: &drand48_data): int = let 
  fun loop (buf: &drand48_data, sum: double, count: int): int = 
    if sum <= 1.0 then loop(buf, sum + random_double(buf), count + 1) else count
in
  loop(buf, 0.0, 0)
end

fn n_attempts (n:int): int = let
  var buf: drand48_data
  val _ = srand48_r(0L, buf)
  fun loop (n:int, count: int, buf: &drand48_data):int =
    if n = 0 then count else loop(n-1, count + attempts(buf), buf)
in
  loop(n, 0, buf)
end

dataviewtype command = 
  | {l:addr} Compute of (int @ l, int @ l -<lin,prf> void | ptr l, int)
  | Quit of ()
// end of [command]

viewtypedef work = command

fun fwork {l:addr}
  (ws: !WORKSHOPptr(work,l), x: &work >> work?): int = 
  case+ x of
  | ~Compute (pf_p, fpf_p | p, iterations) => let 
       val () = !p := n_attempts (iterations)
       prval () = fpf_p (pf_p) // the view is returned to the scheduler
     in 1 end
  | ~Quit () => 0
// end of [fwork]

fun insert_all
  {l,l2:agz} {n:pos} (
    pf_arr: !array_v(int, n, l2)
  | ws: !WORKSHOPptr(work, l), arr: ptr l2, n: int n, iterations: int
  ) : void = let
  fun loop {l,l2:agz} {n:nat} .< n >. (
      pf: !array_v(int, n, l2)
    | ws: !WORKSHOPptr(work, l), 
      p: ptr l2, 
      n: int n, 
      iterations: int)
    : void =
    if n > 0 then let
      prval (pf1, pf2) = array_v_uncons{int}(pf)
      prval (pf_p, fpf_p)  = __borrow(pf1) where {
        extern prfun __borrow
          {l:addr} (pf: !int @ l): (int @ l, int @ l -<lin,prf> void)
      } // end of [prval]
      val () = workshop_insert_work(ws, Compute (pf_p, fpf_p | p, iterations))
      val () = loop(pf2 | ws, p + sizeof<int>, n - 1, iterations)
      prval () = pf := array_v_cons{int}(pf1, pf2)
    in
      // nothing
    end // end of [if]
in
  loop(pf_arr | ws, arr, n, iterations / NCPU)
end // end of [insert_all]

implement main () = let 
//
  val ws = workshop_make<work>(NCPU, fwork)
  var ncpu: int = 0
  val () = while (ncpu < NCPU) let
    val _ = workshop_add_worker(ws) in ncpu := ncpu + 1
  end // end of [val]
// 
  val nworker = workshop_nworker_get(ws)
//
  var !p_arr with pf_arr = @[int][NCPU](0)
//
  val () = insert_all(pf_arr | ws, p_arr, NCPU, ITER)
  val () = workshop_wait_blocked_all(ws)
//
  var j: Nat = 0;
  val () = while (j < nworker) let
    val () = workshop_insert_work(ws, Quit ()) in j := j + 1
  end // end of [val]
  val () = workshop_wait_quit_all(ws)
  val () = workshop_free_vt_exn(ws)
//
  var k: Nat = 0;
  var total: int = 0;
  val () = for (k := 0; k < NCPU; k := k + 1) total := total + p_arr->[k]
  val avg = total / double_of_int(ITER)
  val () = printf("total: %d\n", @(total))
  val () = print(avg)
  val () = print_newline ()
//
in
  // nothing
end // end of [main]

(* ****** ****** *)

(* end of [randomcompec.dats] *)
