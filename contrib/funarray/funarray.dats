(*
**
** An implementation of functional arrays based on Braun trees.
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2008
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt
//

(* ****** ****** *)

staload "funarray.sats"

(* ****** ****** *)

datatype brauntree (a:t@ype+, int) =
  | {n1,n2:nat | n2 <= n1; n1 <= n2+1}
    B (a, n1+n2+1) of (a, brauntree (a, n1), brauntree (a, n2))
  | E (a, 0) of ()

stadef bt = brauntree // an abbreviation

(* ****** ****** *)

assume funarray (a: t@ype, n:int) = brauntree (a, n)

(* ****** ****** *)

implement funarray_nil {a} () = E ()

(* ****** ****** *)

implement funarray_length<a> (A) = size (A) where {
  fun diff {nl,nr:nat | nr <= nl && nl <= nr+1} .<nr>. 
    (nr: int nr, t: bt (a, nl)):<> int (nl-nr) = begin case+ t of
    | B (_, tl, tr) => begin
        if nr > 0 then let
          val nr2 = nr / 2
        in
          if nr > nr2 + nr2 then diff (nr2, tl) else diff (nr2-1, tr)
        end else begin
          1 // return value
        end // end of [if]
      end // end of [B]
     | E () => 0
  end // end of [diff]

  fun size {n:nat} .<n>. (t: bt (a, n)):<> int n = begin
    case+ t of
    | B (_, tl, tr) => begin
        let val nr = size tr in 1 + nr + nr + diff (nr, tl) end
      end // end of [B]
    | E () => 0
  end // end of [size]
} // end of [funarray_length]

(* ****** ****** *)

implement funarray_get_elt_at<a> (A, i) = get_at (A, i) where {
  fun get_at {n,i:nat | i < n} .<n>. (t: bt (a, n), i: int i):<> a =
    if i > 0 then let
      val i2 = i / 2
    in
      if i > i2 + i2 then let
        val+ B (_, tl, _) = t in get_at (tl, i2)
      end else let
        val+ B (_, _, tr) = t in get_at (tr, i2-1)
      end // end of [if]
    end else let
      val+ B (x, _, _) = t in x
    end // end of [if]
} // end of [funarray_get_at]

implement funarray_set_elt_at<a> (A, i, x) = set_at (A, i, x) where {
  fun set_at {n,i:nat | i < n} .<n>.
    (t: bt (a, n), i: int i, x: a):<> bt (a, n) =
    if i > 0 then let
      val+ B (x0, tl, tr) = t; val i2 = i / 2
    in
      if i > i2 + i2 then begin
        B (x0, set_at (tl, i2, x), tr)
      end else begin
        B (x0, tl, set_at (tr, i2-1, x))
      end // end of [if]
    end else let
      val+ B (_, t1, t2) = t in B (x, t1, t2)
    end // end of [if]
} // end of [funarray_set_at]

(* ****** ****** *)

implement funarray_loadd<a> (t, x) = loadd (t, x) where {
  fun loadd {n:nat} .<n>.
    (t: bt (a, n), x: a):<> bt (a, n+1) = begin
    case+ t of
    | B (x0, tl, tr) => B (x0, loadd (tr, x), tl)
    | E () => B (x, E (), E ())
  end // end of [loadd]
} // end of [funarray_loadd]

implement funarray_lorem<a> (t) = lorem (t) where {
  fun lorem {n:int | n > 0} .<n>.
    (t: bt (a, n)):<> bt (a, n-1) = let
    val+ B (x0, tl, tr) = t
  in
    case+ tl of
    | B _ => B (x0, tr, lorem tl) | E () => E ()
  end
} // end of [brauntree_lorem]

implement funarray_lorem_get<a>
  (t, x) = lorem_get (t, x) where {
  fun lorem_get {n:int | n > 0} .<n>.
    (t: bt (a, n), x: &a? >> a):<> bt (a, n-1) = let
    val+ B (x0, tl, tr) = t
  in
    case+ tl of
    | B _ => B (x0, tr, lorem_get (tl, x)) | E () => (x := x0; E ())
  end // end of [lorem_get]
} // end of [funarray_lorem_get]

(* ****** ****** *)

implement funarray_hiadd<a> (t, n, x) = hiadd (t, n, x) where {
  fun hiadd {n:nat} .<n>.
    (t: bt (a, n), n: int n, x: a):<> bt (a, n+1) =
    if n > 0 then let
      val+ B (x0, tl, tr) = t; val n2 = n / 2
    in
      if n > n2 + n2 then begin
        B (x0, hiadd (tl, n2, x), tr)
      end else begin
        B (x0, tl, hiadd (tr, n2-1, x))
      end
    end else begin
      B (x, E (), E ())
    end // end of [if]
  // end of [hiadd]
} // end of [funarray_hiadd]

implement funarray_hirem<a> (t, n) = hirem (t, n) where {
  fun hirem {n:pos} .<n>.
    (t: bt (a, n), n: int n):<> bt (a, n-1) = let
    val+ B (x0, tl, tr) = t; val n2 = n / 2
  in
    case+ tl of
    | B _ => begin
        if n > n2 + n2 then begin
          B (x0, tl, hirem (tr, n2))
        end else begin
          B (x0, hirem (tl, n2), tr)
        end // end of [if]
      end // end of [B]
    | E () => E ()
  end
  // end of [hirem]
} // end of [funarray_hirem]

implement funarray_hirem_get<a>
  (t, n, x) = hirem_get (t, n, x) where {
  fun hirem_get {n:pos} .<n>.
    (t: bt (a, n), n: int n, x: &a? >> a):<> bt (a, n-1) = let
    val+ B (x0, tl, tr) = t; val n2 = n / 2
  in
    case+ tl of
    | B _ => begin
        if n > n2 + n2 then begin
          B (x0, tl, hirem_get (tr, n2, x))
        end else begin
          B (x0, hirem_get (tl, n2, x), tr)
        end // end of [if]
      end // end of [B]
    | E () => (x := x0; E ())
  end
  // end of [hirem_get]
} // end of [funarray_hirem_get]

(* ****** ****** *)

(* end of [funarray.dats] *)
