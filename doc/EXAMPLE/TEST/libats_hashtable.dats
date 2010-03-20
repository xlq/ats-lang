(*

// author: Hongwei Xi (October, 2008)

*)

(* ****** ****** *)

staload RAND = "libc/SATS/random.sats"

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload H = "libats/SATS/hashtable.sats"
staload _(*anon*) = "libats/DATS/hashtable.dats"

(* ****** ****** *)

// dynload "hashtable.dats" // not needed as [ATS_DYNLOADFLAG = 0]

(* ****** ****** *)

(*
** the efficiency gained from inlining the comparison
** function seems to be less than 5% (more like a 3%)
*)

// (*
implement $H.hash_key<int> (x, _) = ulint_of_int (x)
implement $H.equal_key_key<int> (x1, x2, _) = (x1 = x2)
// *)

implement main (argc, argv) = let
  val () = gc_chunk_count_limit_max_set (~1) // infinite
  var n: int = 0
  val () = begin
    if argc >= 2 then n := int_of_string (argv.[1])
  end
  val [n:int] n = int1_of n
  val () = assert_errmsg (n > 0, #LOCATION)
(*
  val () = $RAND.srand48_with_time ()
*)
  typedef key = int and itm = string
  fn hash (x: key):<cloref> ulint = ulint_of_int (x)
  fn eq (x1: key, x2: key):<cloref> bool = (x1 = x2)

  val [l:addr] ptbl = $H.hashtbl_make {int,string} (hash, eq)
  var i: int; val () = for (i := 0; i < n; i := i+1) let
    val key = $RAND.randint n
    val itm = tostring key // val itm = sprintf ("%i", @(key))
    // val () = printf ("key = %i and itm = %s\n", @(key, itm))
  in
    $H.hashtbl_insert<key,itm> (ptbl, key, itm)
  end // end [while]
  val size = $H.hashtbl_size (ptbl)
  val () = begin
    print "size = "; print size; print_newline ()
  end
  val total = $H.hashtbl_total (ptbl)
  val () = begin
    print "total = "; print total; print_newline ()
  end
  val k0 = 0
  val () = printf ("%i\t->\t", @(k0))
  val () = case+ $H.hashtbl_search (ptbl, k0) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
  val k1 = 1
  val () = printf ("%i\t->\t", @(k1))
  val () = case+ $H.hashtbl_search (ptbl, k1) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
  val k10 = 10
  val () = printf ("%i\t->\t", @(k10))
  val () = case+ $H.hashtbl_search (ptbl, k10) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
  val k100 = 100
  val () = printf ("%i\t->\t", @(k100))
  val () = case+ $H.hashtbl_search (ptbl, k100) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
  val k1000 = 1000
  val () = printf ("%i\t->\t", @(k1000))
  val () = case+ $H.hashtbl_search (ptbl, k1000) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
  val k10000 = 10000
  val () = printf ("%i\t->\t", @(k10000))
  val () = case+ $H.hashtbl_search (ptbl, k10000) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
//
  var !p_f = @lam
    (pf: !unit_v | k: key, i: &itm): void =<clo> i := sprintf ("%i", @(k+k+1))
  // end of [var]
  prval pf = unit_v ()
  val () = $H.hashtbl_foreach_clo<key,itm> {unit_v} (pf | ptbl, !p_f)
  prval unit_v () = pf
//
  val () = printf ("%i\t->\t", @(k10000))
  val () = case+ $H.hashtbl_search (ptbl, k10000) of
    | ~Some_vt s => (print "Some("; print s; print ")")
    | ~None_vt _ => (print "None()")
  val () = print_newline ()
//
  val () = $H.hashtbl_clear (ptbl)
  val () = $H.hashtbl_free_exn (ptbl)  
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [test.dats] *)
