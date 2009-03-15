(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

local

staload TL = "templab.sats"

typedef temp = $TL.temp_t
typedef templst = List temp
typedef label = $TL.label_t
typedef lablst = List label

in

datatype instr =
  | INSTRoper of (
      string(*asm*)
    , templst(*dst*)
    , templst(*src*)
    , lablst(*jump*)
    ) // end of [INSTRoper]
  | INSTRlabel of (string(*asm*), label)
  | INSTRmove of (
      string(*asm*), temp(*dst*), temp(*dst*)
    ) // end of [INSTRmove]

typedef instrlst = List instr

// Instead of turning an instruction into a string and then print it out,
// it should make a lot more sense to print out the instruction directly,
// right?
fun instr_format (fmt: temp -<cloref1> string, ins: instr): string

end // end of [local]

(* ****** ****** *)

(* end of [assembly.sats] *)
