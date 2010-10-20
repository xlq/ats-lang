(*
** some testing code for functions declared in
** libc/SATS/dirent.sats
*)

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2009

(* ****** ****** *)

staload "libc/SATS/stdlib.sats"
staload "libc/SATS/dirent.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/lazy_vt.dats"

(* ****** ****** *)

%{^
ATSinline()
ats_void_type
print_dirent_d_name (ats_ref_type p_ent) {
  printf (((ats_dirent_type*)p_ent)->d_name) ; return ;
} // end of [print_dirent_d_name]
%} // end of [%{^]

extern
fun print_dirent_d_name
  (ent: &dirent): void = "print_dirent_d_name"
// end of [print_dirent_d_name]
extern
fun print_direntptr (p: &direntptr_gc): void = "print_direntptr"
  
implement
print_direntptr (p) = let
  prval pf_ent = p.1 // p = (pf_gc, pf | p_ent)
  val () = print_dirent_d_name !(p.2)
in
  p.1 := pf_ent
end // end of [print_direntptr]

(* ****** ****** *)

%{^
static inline
ats_int_type
compare_direntptr_direntptr (ats_ref_type p1, ats_ref_type p2) {
  return strcoll (
    (*((ats_dirent_type**)p1))->d_name, (*((ats_dirent_type**)p2))->d_name
  ) ; // end of [return]
} // end of [print_dirent_d_name]
%} // end of [%{^]

extern
fun compare_direntptr_direntptr
  (p1: &direntptr_gc, p2: &direntptr_gc):<> int = "compare_direntptr_direntptr"
// end of [compare_direntptr_direntptr]

(* ****** ****** *)

fn prerr_usage (cmd: string): void =
  prerrf ("Usage: %s [dirname]\n", @(cmd))
// end of [prerr_usage]

fn ls (dirname: string): void = let
  val (pfopt_dir | p_dir) = opendir_err (dirname)
in
  if (p_dir > null) then let
    prval Some_v (pf_dir) = pfopt_dir
    val ents = direntptr_stream_vt_make_DIR (pf_dir | p_dir)
    val [n:int] (nent, ents) = list_vt_of_stream_vt<direntptr_gc> (ents)
    val nent_sz = size1_of_int1 (nent)
    var !p_arr with pf_arr = @[direntptr_gc][nent]()
    val () = loop_init {direntptr_gc} (pf_arr | p_arr, ents) where {
      fun loop_init {a:viewtype} {n:nat} {l:addr} .<n>. (
          pf_arr: !array_v (a?, n, l) >> array_v (a, n, l)
        | p: ptr l, xs: list_vt (a, n)
        ) : void = case+ xs of
        | ~list_vt_cons (x, xs) => let
            prval (pf1_at, pf2_arr) = array_v_uncons {a?} (pf_arr)
            val () = !p := x
            val () = loop_init {a} (pf2_arr | p+sizeof<a>, xs)
          in
            pf_arr := array_v_cons {a} (pf1_at, pf2_arr)
          end // end of [list_vt_cons]
        | ~list_vt_nil () => let
            prval () = array_v_unnil {a?} (pf_arr)
          in
            pf_arr := array_v_nil {a} ()
          end // end of [list_vt_nil]
      // end of [loop]
    } // end of [val]

    val () = qsort {direntptr_gc}
      (!p_arr, nent_sz, sizeof<direntptr_gc>, compare_direntptr_direntptr)
    // end of [qsort]

    val () = printf (
      "The entries in the directory [%s] are listed as follows:\n", @(dirname)
    ) // end of [val]

    prval pf = unit_v ()
    val () = array_ptr_foreach_clo_tsz
      (pf | !p_arr, !p_f, nent_sz, sizeof<direntptr_gc>) where {
      var !p_f = @lam (pf: !unit_v | p_ent: &direntptr_gc)
        : void =<clo> begin
          $effmask_all (print_direntptr (p_ent); print_newline ())
        end // end of [@lam]
    } // end of [val]
    prval unit_v () = pf
    
    prval pf = unit_v ()
    val () = array_ptr_clear_clo_tsz
      {direntptr_gc} (pf | !p_arr, nent_sz, !p_f, sizeof<direntptr_gc>) where {
      var !p_f = @lam
        (pf: !unit_v | p: &direntptr_gc >> direntptr_gc?)
        : void =<clo> ptr_free (p.0, p.1 | p.2)
    } // end of [val]
    prval unit_v () = pf
  in
    printf ("There are %i entries in the directory [%s]\n", @(nent, dirname))
  end else let
    prval None_v () = pfopt_dir
  in
    printf ("*** ERROR ***: the directory [%s] cannot be opened\n", @(dirname))
  end // end of [if]
end // end of [ls]

// listing all of the files in a given directory
implement main (argc, argv) = let
  val () = if (argc < 2) then prerr_usage (argv.[0])
  val () = assert (argc >= 2); val dirname = argv.[1]
  var i: Nat // uninitialized
in
  for (i := 1; i < argc; i := i+1) ls (argv.[i])
end // end of [main]

(* ****** ****** *)

(* end of [libc_dirent.dats] *)
