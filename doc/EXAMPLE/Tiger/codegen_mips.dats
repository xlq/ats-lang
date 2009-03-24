(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload TL = "templab.sats"
typedef temp = $TL.temp_t
typedef templst = $TL.templst

(* ****** ****** *)

staload FRM = "frame.sats"
typedef frame = $FRM.frame_t

staload ASM = "assem.sats"

(* ****** ****** *)

staload "irtree.sats"

(* ****** ****** *)

staload "codegen.sats"

(* ****** ****** *)

val theCallDefReglst = (
  $FRM.theSpecialReglst + $FRM.theCallersavedReglst
) : List temp

(* ****** ****** *)

val WORDSIZE = $FRM.WORDSIZE_get ()

viewtypedef instrlst_vt = List_vt ($ASM.instr)

fn instrlst_add_stm
  (frm: frame, res: &instrlst_vt, stm: stm): void = let
  typedef instr = $ASM.instr
  fn emit (res: &instrlst_vt, ins: instr): void =
    res := list_vt_cons (ins, res)
  // end of [emit]
  fun auxstm (res: &instrlst_vt, stm: stm): void = let
(*
    val () = begin
      prerr "auxstm: stm = "; prerr_stm stm; prerr_newline ()
    end // end of [val]
*)
  in
    case+ stm of
    | STMseq (stm1, stm2) => let
        val () = auxstm (res, stm1); val () = auxstm (res, stm2)
      in
        // empty
      end // end of [STMseq]
    | STMmove (EXPmem (e1), e2) => let
        val s0 = auxexp (res, e1); val s1 = auxexp (res, e2)
        val asm = "sw `s1, 0(`s0)"
        val src = '[s0, s1] and dst = '[]; val jump= None ()
      in
        emit (res, $ASM.INSTRoper (asm, src, dst, jump))
      end // end of [STMmove (EXPmem, _)]
    | STMmove (EXPtemp d0, e2) => let
        val s0 = auxexp (res, e2)
        val asm = "move `d0, `s0" // "addiu `d0, `s0, 0"
        val src = s0 and dst = d0
      in
        emit (res, $ASM.INSTRmove (asm, src, dst))
      end // end of [STMmove (EXPtemp, _)]
    | STMjump (e, labs) => begin case+ e of
      | EXPname lab => let
          val asm = "j " + $TL.label_name_get lab
          val src = '[] and dst = '[]; val jump = Some '[lab]
        in
          emit (res, $ASM.INSTRoper (asm, src, dst, jump))
        end // end of [EXPname]
      | _ => let
          val s0 = auxexp (res, e)
          val asm = "jr `s0"
          val src = '[s0] and dst = '[]; val jump = Some labs
        in
          emit (res, $ASM.INSTRoper (asm, src, dst, jump))
        end // end of [_]
      end (* end of [STMjump] *)
    | STMcjump (relop, e1, e2, tlab, flab) => let
        val opcode = case+ relop of
          | EQ  _ => "beq"
          | NEQ _ => "bne"
          | GT  _ => "bgt"
          | GE  _ => "bge"
          | LT  _ => "blt"
          | LE  _ => "ble"
        // end of [val]
        val s0 = auxexp (res, e1)
        val s1 = auxexp (res, e2)
        val asm = opcode + " `s0, `s1, `j0"
        val src = '[s0, s1] and dst = '[]
        val jump = Some '[tlab, flab]
      in
        emit (res, $ASM.INSTRoper (asm, src, dst, jump))
      end // end of [STMcjump]
    | STMlabel lab => let
        val asm = $TL.label_name_get (lab) + ":"
      in
        emit (res, $ASM.INSTRlabel (asm, lab))
      end // end of [STMlabel]
    | STMexp e => begin
        let val _(*tmp*) = auxexp (res, e) in () end
      end // end of [STMexp]
    | _ => begin
        prerr "INTERNAL ERROR";
        prerr ": auxstm: stm = "; prerr_stm stm; prerr_newline ();
        exit {void} (1)
      end // end of [_]
  end // end of [auxstm]

  and auxexp (res: &instrlst_vt, exp: exp): temp = let
(*
    val () = begin
      prerr "auxexp: exp = "; prerr_exp exp; prerr_newline ()
    end // end of [val]
*)
  in
    case+ exp of
    | EXPconst i => let
        val d0 = $TL.temp_make_new ()
        val asm = "li `d0, " + tostring_int i
        val src = '[] and dst = '[d0]; val jump = None ()
      in
        emit (res, $ASM.INSTRoper (asm, src, dst, jump)); d0        
      end // end of [EXPconst]
    | EXPname lab => let
        val d0 = $TL.temp_make_new ()
        val asm = "la `d0, " + $TL.label_name_get (lab)
        val src = '[] and dst = '[d0]; val jump = None ()
      in
        emit (res, $ASM.INSTRoper (asm, src, dst, jump)); d0        
      end // end of [EXPname]
    | EXPtemp t => t
    | EXPbinop (binop, e1, e2) => let
        val opcode = case binop of
          | PLUS _  => "add"
          | MINUS _ => "sub"
          | MUL _   => "mul"
          | DIV _   => "div"
        // end of [val]
        val s0 = auxexp (res, e1); val s1 = auxexp (res, e2)
        val d0 = $TL.temp_make_new ()
        val asm = opcode + " `d0, `s0, `s1"
        val src = '[s0, s1] and dst = '[d0]; val jump = None ()
      in
        emit (res, $ASM.INSTRoper (asm, src, dst, jump)); d0
      end // end of [EXPbinop]
    | EXPmem (e) => let
        val s0 = auxexp (res, e)
        val d0 = $TL.temp_make_new ()
        val asm = "lw `d0, 0(`s0)"
        val src = '[s0] and dst = '[d0]; val jump = None ()
      in
        emit (res, $ASM.INSTRoper (asm, src, dst, jump)); d0
      end // end of [EXPmem]
    | EXPcall (e_fun, es_arg) => let
        val s_fun = auxexp (res, e_fun)
        val ss_arg = auxarglst (res, es_arg)
        val nWORDSIZE = loop (ss_arg, 0) where {
          fun loop (tmps: templst, ofs: int): int = case+ tmps of
            | list_cons (_, tmps) => loop (tmps, ofs + WORDSIZE)
            | list_nil () => ofs
          // end of [loop]
        } // end of [val]
//
        val () = let
          val src = '[] and dst = '[]; val jump = None ()
          val asm = sprintf ("sub $sp, $sp, %i", @(nWORDSIZE))
        in
          emit (res, $ASM.INSTRoper (asm, src, dst, jump))
        end // end of [val]
//
        val () = loop1 (res, ss_arg, $FRM.theFunargReglst, 0) where {
          fn* loop1 (
              res: &instrlst_vt, tmps: templst, fars: templst, ofs: int
            ) : void =
            case+ tmps of
            | list_cons (tmp, tmps) => begin case+ fars of
              | list_cons (far, fars) => let
                  val src = '[tmp] and dst = '[far]; val jump = None ()
                  val asm = "move `d0, `s0"
                  val () = emit (res, $ASM.INSTRoper (asm, src, dst, jump))
                in
                  loop1 (res, tmps, fars, ofs + WORDSIZE)
                end // end of [list_cons]
              | list_nil () => loop2 (res, tmp, tmps, ofs)
              end // end of [list_cons]
            | list_nil () => ()
          // end of [loop1]
          and loop2 ( // not tail-recursive
              res: &instrlst_vt, tmp: temp, tmps: templst, ofs: int
            ) : void = let
            val () = case+ tmps of
              | list_cons (tmp1, tmps1) => 
                  loop2 (res, tmp1, tmps1, ofs + WORDSIZE)
              | list_nil () => ()
            // end of [val]
            val src = '[tmp] and dst = '[]; val jump = None ()
            val asm = sprintf ("sw `s0, %i($sp)", @(ofs))
          in
            emit (res, $ASM.INSTRoper (asm, src, dst, jump))
          end // end of [loop2]
        } // end of [val]
        val src = list_cons (s_fun, ss_arg)
        val dst = theCallDefReglst; val jump = None ()
        val asm = "call `s0"
        val () = emit (res, $ASM.INSTRoper (asm, src, dst, jump))
//
        val () = let
          val src = '[] and dst = '[]; val jump = None ()
          val asm = sprintf ("add $sp, $sp, %i", @(nWORDSIZE))
        in
          emit (res, $ASM.INSTRoper (asm, src, dst, jump))
        end // end of [val]
//
      in
        $FRM.RV // where the return value is stored
      end // end of [EXPcall]
    | _ => begin
        prerr "INTERNAL ERROR";
        prerr "auxexp: exp = "; prerr_exp exp; prerr_newline ();
        exit {temp} (1)
      end // end of [_]
  end // end of [auxexp]
  
  and auxarglst
    (res: &instrlst_vt, args: explst): List temp = case+ args of
    | list_cons (arg, args) => let
        val s_arg = auxexp (res, arg); val ss_arg = auxarglst (res, args)
      in
        list_cons (s_arg, ss_arg)
      end // end of [list_cons]
    | list_nil () => list_nil ()
  // end of [auxarglst]
in
  auxstm (res, stm)
end // end of [instrlst_add_stm]

(* ****** ****** *)

(* end of [codegen_mips.dats] *)
