(*
** Specifying Finite Lists
*)

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"

(* ****** ****** *)

staload DNODE = "dnode.sats"
sortdef dnode = $DNODE.dnode

(* ****** ****** *)

sortdef clist = ilist
datasort file = // abstract

absprop name_p (file, clist)
absprop dnode_p (file, dnode)

(* ****** ****** *)

praxi
FILE_name_axiom
  {f:file} {cs:clist} {n:int} (
  pf: name_p (f, cs), pflen: LENGTH (cs, n)
) : [n >= 1] void

(* ****** ****** *)

(* end of [file.sats] *)
