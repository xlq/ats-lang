(*
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: May, 2011
//
*)

(* ****** ****** *)

staload FS = "libats/SATS/funset_listord.sats"
staload _(*anon*) = "libats/DATS/funset_listord.dats"

(* ****** ****** *)

staload Time = "libc/SATS/time.sats"
staload Rand = "libc/SATS/random.sats"

(* ****** ****** *)

(*
** the efficiency gained from inlining the comparison
** function seems to be less than 5%.
*)

implement
$FS.compare_elt_elt<int> (x1, x2, _(*cmp*)) =
  if x1 < x2 then ~1 else if x1 > x2 then 1 else 0

implement main (argc, argv) = let
  val () = gc_chunk_count_limit_max_set (~1) // infinite
  var n: int = 0
  val () = begin
    if argc >= 2 then n := int_of_string (argv.[1])
  end // end of [val]
  val [n:int] n = int1_of n; val n2 = n / 2
  val () = assert (n > 0)
  val () = $Rand.srand48_with_time ()
  fn cmp (x1: int, x2: int):<cloref> Sgn = compare (x1, x2)

  var ints1: $FS.set (int) = $FS.funset_make_nil ()
  var i: int; val () =
    for (i := 0; i < n2; i := i+1) {
      val _ = $FS.funset_insert<int> (ints1, $Rand.randint n, cmp)
    }
  // end [val]
  val size1 = $FS.funset_size (ints1)
  val () = begin
    print "size1 = "; print size1; print_newline ()
  end
(*
  val height1 = $FS.funset_height (ints1)
  val () = begin
    print "height1 = "; print height1; print_newline ()
  end
*)

  var ints2: $FS.set (int) = $FS.funset_make_nil ()
  var i: int; val () =
    for (i := n2; i < n; i := i+1) {
      val _ = $FS.funset_insert<int> (ints2, $Rand.randint n, cmp)
    }
  // end [val]
  val size2 = $FS.funset_size (ints2)
  val () = begin
    print "size2 = "; print size2; print_newline ()
  end
(*
  val height2 = $FS.funset_height (ints2)
  val () = begin
    print "height2 = "; print height2; print_newline ()
  end
*)

  val ints_union = $FS.funset_union (ints1, ints2, cmp)
  val size = $FS.funset_size (ints_union)
  val () = begin
    print "size(ints_union) = "; print size; print_newline ()
  end
(*
  val height = $FS.funset_height (ints)
  val () = begin
    print "height(union) = "; print height; print_newline ()
  end
*)

  val e_recip = 1.0 - (double_of size) / n
  val e = 1.0 / e_recip; val () = begin
    print "the constant e = "; print e; print_newline ()
  end

  val ints_intersect = $FS.funset_intersect (ints1, ints2, cmp)
  val size = $FS.funset_size (ints_intersect)
  val () = begin
    print "size(intersect) = "; print size; print_newline ()
  end

  val ints_diff12 = $FS.funset_diff (ints1, ints2, cmp)
  val size = $FS.funset_size (ints_diff12)
  val () = begin
    print "size(ints_diff12) = "; print size; print_newline ()
  end

  val ints_diff21 = $FS.funset_diff (ints2, ints1, cmp)
  val size = $FS.funset_size (ints_diff21)
  val () = begin
    print "size(ints_diff21) = "; print size; print_newline ()
  end

  val ints_symdiff = $FS.funset_symdiff (ints1, ints2, cmp)
  val size = $FS.funset_size (ints_symdiff)
  val () = begin
    print "size(ints_symdiff) = "; print size; print_newline ()
  end

  val () = print "checking: ints_diff12 \\cup ints_diff12 = ints_symdiff:\n"
  val () = assert (
    $FS.funset_is_equal (
      $FS.funset_union (ints_diff12, ints_diff21, cmp)
    , ints_symdiff
    , cmp
    ) (* end of [funset_is_equal] *)
  ) (* end of [assert] *)
  val () = print "checking is done successfully.\n"

  val () = print "checking: ints_union \\backslash ints_intersect = ints_symdiff:\n"
  val () = assert (
    $FS.funset_is_equal (
      $FS.funset_diff (ints_union, ints_intersect, cmp), ints_symdiff, cmp
    ) (* end of [funset_is_equal] *)
  ) (* end of [assert] *)
  val () = print "checking is done successfully.\n"

in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [libats_funset_listord.dats] *)
