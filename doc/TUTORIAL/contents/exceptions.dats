//
//
// code for illustration in exceptions.dats
//
//

(* ****** ****** *)

exception Fail // Fail: exn
exception Fail_msg of string // Fail_msg: string -> exn

// Fail_msgs : {n:nat} (int n, list (string n)) -> exn
exception {n:nat} Fail_msgs of (int n, list (string, n))

(* ****** ****** *)

datatype bt = E | B of (bt, bt) // datatype for binary trees

fn isBraunTree (bt0: bt): bool = let
  exception NotBraunTree
  fun aux (bt: bt): int = case+ bt of
    | B (bt1, bt2) => let
        val ls = aux bt1 and rs = aux bt2
      in
        if (ls >= rs && rs+1 >= ls) then ls+rs+1 else $raise NotBraunTree()
      end
    | E () => 0
in
  try let val s = aux bt0 in true end with ~NotBraunTree() => false
end // end of [isBraunTree]

(* ****** ****** *)

fn{a:t@ype} nth (xs: List a, n: Nat): a = let
  exception Found of a
  fn f (i: Nat, x: a):<cloptr1> void = if i = n then $raise (Found x)
in
  try list_iforeach_cloptr (xs, f); $raise ListSubscriptException ()
  with ~Found x => x
end // end of [nth]

(* ****** ****** *)

fn{a:t@ype} nth (xs: List a, n: Nat): a = let
  exception Found
  val ans = ref_make_elt<Option a> (None)
  fn f (i: Nat, x: a):<cloptr1> void =
    if i = n then (!ans := Some x; $raise Found ())
in
  try list_iforeach_cloptr (xs, f) with ~Found () => ();
  case !ans of
    | Some x => x | None () => $raise ListSubscriptException ()
end // end of [nth]

(* ****** ****** *)

(* end of [exceptions.dats] *)
