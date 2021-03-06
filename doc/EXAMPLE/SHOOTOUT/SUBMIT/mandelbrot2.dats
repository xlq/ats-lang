(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -D_GNU_SOURCE -D_ATS_MULTITHREAD -lpthread -msse2 -O3 mandelbrot2.dats -o mandelbrot2
**
*)

(* ****** ****** *)

#define TIMES 50
#define LIMIT 2.0; #define LIMIT2 (LIMIT * LIMIT)

(* ****** ****** *)

staload "libc/SATS/SIMD_v2df.sats" // no dynamic loading

(* ****** ****** *)

staload "libc/SATS/sched.sats"
staload TYPES = "libc/sys/SATS/types.sats"
macdef pid_t = $TYPES.pid_of_int

staload "libats/SATS/parworkshop.sats"
staload _ = "libats/DATS/parworkshop.dats"

(* ****** ****** *)

viewtypedef work = () -<lincloptr1> void
viewtypedef WSptr (l:addr) = WORKSHOPptr (work, l)

(* ****** ****** *)

fun fwork {l:agz}
  (ws: !WSptr l, wk: &work >> work?): int = let
  val wk = wk
  val pfun = __cast (wk) where {
    extern castfn __cast
      (wk: !work >> opt (work, i >= 1)): #[i:nat] uintptr i
  } // end of [val]
in
  if pfun >= (uintptr1_of_uint1)1U then let
    prval () = opt_unsome {work} (wk)
    val () = wk ()
    val () = cloptr_free (wk)
  in
    1 // the worker is to continue
  end else let
    val u = uint1_of_uintptr1 (pfun)
    val i = int_of_uint (u)
    prval () = opt_unnone {work} (wk)
    prval () = cleanup_top {work} (wk)
  in
    ~i // the worker is to pause or quit
  end // end of [if]
end // end of [fwork]

(* ****** ****** *)

#define i2d double_of_int

%{^
ATSinline()
ats_void_type output_byte (
  ats_ptr_type A, ats_int_type i, ats_byte_type b
) {
  ((char*)A)[i] = b ; return ;
} // end of [output_byte]
%}
extern
fun output_byte (A: ptr, i: int, b: byte): void = "output_byte"
// end of [output_byte]

(* ****** ****** *)

fn mandelbrot {l:agz}
  (ws: !WSptr l, A: ptr, h: int, w: int): void = let

  val h_rcp = 1.0 / (i2d h) and w_rcp = 1.0 / (i2d w)
  
  fun test (x: int, y: int):<cloref1> int = let
    val x2 = i2d (x << 1)
    val Cr0 = x2 * w_rcp - 1.5
    val Cr1 = (x2 + 2.0) * w_rcp - 1.5
    val y2 = i2d (y << 1)
    val Ci0 = y2 * h_rcp - 1.0
    val Ci1 = Ci0
    val Crv = v2df_make (Cr0, Cr1)
    val Civ = v2df_make (Ci0, Ci1)
  
    fun loop (
        eo: int
      , Cr: double, Ci: double, Zr: double, Zi: double
      , times: int
      ) :<fun1> int = let
      val Tr = Zr * Zr and Ti = Zi * Zi; val Tri = Tr + Ti
    in
      case+ 0 of
      | _ when Tri <= LIMIT2 => begin
          if times = 0 then eo else let
            val Zr_new = Tr - Ti + Cr; val Zi_new = 2.0 * (Zr * Zi) + Ci
          in
            loop (eo, Cr, Ci, Zr_new, Zi_new, times-1)
          end // end of [if]
        end // end of [_ when ...]
      | _ => 0
    end // end of [loop]
  
    fun loopv
      (Zrv: v2df, Ziv: v2df, times: int):<cloref1> int = let
      val Trv = Zrv * Zrv and Tiv = Ziv * Ziv; val Triv = Trv + Tiv
      val Tri0 = v2df_get_fst (Triv) and Tri1 = v2df_get_snd (Triv)
      val Zrv_new = Trv - Tiv + Crv
      val Ziv_new = (x + x) + Civ  where { val x = Zrv * Ziv }
    in
      case+ 0 of
      | _ when Tri0 <= LIMIT2 => begin case+ 0 of
        | _ when Tri1 <= LIMIT2 => begin
            if times = 0 then 0x3 else loopv (Zrv_new, Ziv_new, times-1)
          end // end of [_ when ...]
        | _ => begin
            if times = 0 then 0x2 else let
              val Zr0_new = v2df_get_fst (Zrv_new) and Zi0_new = v2df_get_fst (Ziv_new)
            in
              loop (0x2(*eo*), Cr0, Ci0, Zr0_new, Zi0_new, times-1)
            end // end of [if]
          end // end of [_]
        end // end of [_ when ...]
      | _ => begin case+ 0 of
        | _ when Tri1 <= LIMIT2 => begin
            if times = 0 then 0x1 else let
              val Zr1_new = v2df_get_snd (Zrv_new) and Zi1_new = v2df_get_snd (Ziv_new)
            in
              loop (0x1(*eo*), Cr1, Ci1, Zr1_new, Zi1_new, times-1)
            end // end of [if]
          end // end of [_ when ...]
        | _ => 0x0 // return value
        end // end of [_]
    end // end of [loopv]
  in
    loopv (v2df_0_0, v2df_0_0, TIMES)
  end // end of [test]
  
  #define i2b byte_of_int
  fun output_one (
      x: int, y: int, i: int, b: byte, n: natLte 8
    ) :<cloref1> void =
    if x < w then let
      val res = test (x, y); val res = i2b res in
      case+ 0 of
      | _ when n >= 2 => begin
          output_one (x + 2, y, i, (b << 2) + res, n - 2)
        end // end of [_ when ...]
      | _ (*n=0*) => let
          val () = output_byte (A, i, b) // A[i] = b
        in
          output_one (x + 2, y, i+1, res, 6)
        end // end of [_]
    end else begin
      output_byte (A, i, b << n)
    end // end of [if]
  // end of [output_one]
  
  macdef byte = byte_of_int
  val () = output_all (ws, 0) where {
    fun output_all {l:agz}
      (ws: !WSptr l, y: int):<cloref1> void =
      if y < h then let
        val () = workshop_insert_work (ws, f) where {
          val i = y * ((w + 7) / 8)
          val f = lam (): void =<lincloptr1> output_one (0, y, i, (byte)0, 8)
        } // end of [val]
      in
        output_all (ws, y+1) 
      end // end of [if]
    // end of [output_all]
  } // end of [val]  
  val () = workshop_wait_blocked_all (ws)
in
  // nothing
end // end of [mandelbrot]

(* ****** ****** *)

fun ncore_get (): int = let
  var cs: cpu_set0_t // uninitialized
  prval () = cpusetinit (cs) // not a real initialization
  stavar nset: int
  val nset = cpusetsize_get (cs)
  val err = sched_getaffinity ((pid_t)0, nset, cs)
  val () = assert_errmsg (nset >= 2, #LOCATION)
  var count: Nat = 0
  var i: Nat // uninitialized
  val () = for* (cs: cpu_set_t nset) =>
    (i := 0; i < 16; i := i + 1)
    if (CPU_ISSET (i, cs) > 0) then (count := count + 1)
  // end of [val]
in
  count
end // end of [ncore_get]

(* ****** ****** *)

%{^
ats_void_type
print_bytearr (
  ats_ptr_type A, ats_size_type sz
) {
  int n, lft = sz ;
  while (lft > 0) { n = fwrite (A, 1, lft, stdout) ; lft -= n ; }
  return ;
} // end of [print_bytearr]
%} // end of [%{^]


#define QSZ 1024

implement main (argc, argv) = let
  val () = assert_errmsg_bool1
    (argc >= 2, "Exit: wrong command format!\n")
  val i = int1_of_string (argv.[1])
  val () = assert_errmsg_bool1
    (i >= 2, "The input integer needs to be at least 2.\n")
//
  val ncore = ncore_get ()
  val nworker =
    (if (argc >= 3) then int_of argv.[2] else ncore): int
  // val () = (prerr "nworker = "; prerr nworker; prerr_newline ())
  val nworker = int1_of_int (nworker)
  val () = assert_errmsg (nworker > 0, #LOCATION)
  val ws = workshop_make<work> (QSZ, fwork)
  val _err = workshop_add_nworker (ws, nworker)
  val () = assert_errmsg (_err = 0, #LOCATION)
//
  val h = i
  val w8 = (i + 7) / 8
  val sz = h nmul w8
  val sz = size1_of_int1 (sz)
  val [l0:addr] (pfgc, pfarr | p) = malloc_gc (sz)
  val () = mandelbrot (ws, p, i, i)
  extern fun print_bytearr (A: ptr, sz: size_t): void = "print_bytearr"
  val () = begin
    printf ("P4\n%i %i\n", @(i, i)); if (h > 0) then print_bytearr (p, sz)
  end // end of [val]
  val () = free_gc (pfgc, pfarr | p)
//
  var i: Nat = 0
  val () = while (i < nworker) let
    val _quit = $extval (work, "(void*)0")
    val () = workshop_insert_work (ws, _quit) in i := i + 1
  end // end of [val]
  val () = workshop_wait_quit_all (ws)
  val () = workshop_free_vt_exn (ws)
in
  // nothing
end // end of [main]

(* ****** ****** *)

(* end of [mandelbrot2.dats] *)
