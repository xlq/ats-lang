(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload Err = "error.sats"

staload TL = "templab.sats"
typedef temp = $TL.temp_t
typedef templst = $TL.templst
viewtypedef templst_vt = List_vt (temp)

(* ****** ****** *)

staload FRM = "frame.sats"
typedef frame = $FRM.frame_t

staload ASM = "assem.sats"

(* ****** ****** *)

staload "irtree.sats"

(* ****** ****** *)

staload "codegen.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"
staload _(*anonymous*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

val WORDSIZE = $FRM.WORDSIZE_get ()

viewtypedef instrlst_vt = List_vt ($ASM.instr)

(* ****** ****** *)

fn instrlst_add_stm
  (frm: frame, res: &instrlst_vt, stm: stm): void = let
  typedef instr = $ASM.instr
  fn emit (res: &instrlst_vt, ins: instr): void =
    res := list_vt_cons (ins, res)
  // end of [emit]

  // AT&T-style of syntax is used for the assembly code
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
    | STMjump (e, labs) => begin case+ e of
      | EXPname lab => let
          val asm = "jmp ." + $TL.label_name_get lab
          val src = '[] and dst = '[]; val jump = Some '[lab]
        in
          emit (res, $ASM.INSTRoper (asm, src, dst, jump))
        end // end of [EXPname]
      | _ => let
          val s0 = auxexp (res, e)
          val asm = "jmp `s0"
          val src = '[s0] and dst = '[]; val jump = Some labs
        in
          emit (res, $ASM.INSTRoper (asm, src, dst, jump))
        end // end of [_]
      end (* end of [STMjump] *)
    | STMcjump (relop, e1, e2, tlab, flab) => let
        val opcode = (case+ relop of
          | EQ  _ => "je"
          | NEQ _ => "jne"
          | GT  _ => "jg"
          | GE  _ => "jge"
          | LT  _ => "jl"
          | LE  _ => "jle"
        ) : string // end of [val]
        val s0 = auxexp (res, e1)
        val s1 = auxexp (res, e2)
        val () = emit
          (res, $ASM.INSTRoper (asm, src, dst, jump)) where {
           val asm = "cmpl `s0, `s1"
           val src = '[s0, s1] and dst = '[]; val jump = None ()
        } // end of [val]
        val () = emit
          (res, $ASM.INSTRoper (asm, src, dst, jump)) where {
          val asm = opcode + " `j0"
          val src = '[s0, s1] and dst = '[]; val jump = Some '[tlab, flab]
        } // end of [val]
      in
        // empty
      end // end of [STMcjump]
    | STMmove (EXPmem (e1), e2) => let
        val s0 = auxexp (res, e1); val s1 = auxexp (res, e2)
        val () = emit
          (res, $ASM.INSTRoper (asm, src, dst, jump)) where {
          val asm = "movl `s1, 0(`s0)"
          val src = '[s0, s1] and dst = '[]; val jump= None ()
        } // end of [val]
      in
        // empty
      end // end of [STMmove (EXPmem, _)]
    | STMmove (EXPtemp t1, e2) => let
        val d0 = t1; val s0 = auxexp (res, e2)
        val () = emit
          (res, $ASM.INSTRmove (asm, src, dst)) where {
          val asm = "movl `s0, `d0"; val src = s0 and dst = d0
        } // end of [val]
      in
        // empty
      end // end of [STMmove (EXPtemp, _)]
    | STMlabel lab => let
        val name = $TL.label_name_get lab
        val asm = sprintf (".%s:", @(name))
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
        val asm = sprintf ("movl $%i, `d0", @(i))
        val src = '[] and dst = '[d0]; val jump = None ()
      in
        emit (res, $ASM.INSTRoper (asm, src, dst, jump)); d0        
      end // end of [EXPconst]
    | EXPname lab => let
        val d0 = $TL.temp_make_new ()
        val name = $TL.label_name_get (lab)
        val asm = sprintf ("movl .%s, `d0", @(name))
        val src = '[] and dst = '[d0]; val jump = None ()
      in
        emit (res, $ASM.INSTRoper (asm, src, dst, jump)); d0        
      end // end of [EXPconst]
    | EXPtemp t => t
    | EXPbinop (binop, e1, e2)
        when binop_is_additive binop => let
        val opcode = (case+ binop of
          | PLUS _ => "addl" | MINUS _ => "subl" | _ => $Err.abort {string} (1)
        ) : string // end of [val]
        val s0 = auxexp (res, e1)
        val s1 = auxexp (res, e2)
        val () = emit
          (res, $ASM.INSTRoper (asm, src, dst, jump)) where {
          val asm = opcode + " `s1, `s0"
          val src = '[s0, s1] and dst = '[s0]; val jump = None ()
        } // end of [val]
      in
        s0 // the return value
      end (* end of [val] *)
    | EXPmem (e) => let
        val s0 = auxexp (res, e)
        val d0 = $TL.temp_make_new ()
        val () = emit
          (res, $ASM.INSTRoper (asm, src, dst, jump)) where {
          val asm = "movl (`s0), `d0"
          val src = '[s0] and dst = '[d0]; val jump = None ()
        } // end of [val]
      in
        d0 // the return value
      end // end of [EXPmem]
    | EXPcall (e_fun, es_arg) => let
        val s_fun = auxexp (res, e_fun)
        val (tmps, ss_arg) = auxarglst (res, es_arg)
        val ss_arg = list_of_list_vt (ss_arg)
        val () = emit
          (res, $ASM.INSTRoper (asm, src, dst, jump)) where {
          val asm = "call `s0"
          val src = list_cons (s_fun, ss_arg) and dst = '[]
          val jump = None ()
        } // end of [val]
        val () = loop
          (res, $FRM.theFunargReglst, tmps) where {
          fun loop (
            res: &instrlst_vt, fars: templst, tmps: templst_vt
            ) : void = case+ (fars, tmps) of
            | (list_cons (far, fars), ~list_vt_cons (tmp, tmps)) => let
                val () = emit
                  (res, $ASM.INSTRmove (asm, src, dst)) where {
                  val asm = "movl `s0, `d0"; val src = tmp and dst = far
                } // end of [val]
              in
                loop (res, fars, tmps)
              end // end of [list_cons, list_cons]
            | (fars, tmps) => list_vt_free (tmps)
          // end of [loop]
        } // end of [val]
      in
        $FRM.RV
      end // end of [EXPcall]
    | _ => begin
        prerr "INTERNAL ERROR";
        prerr ": auxexp: exp = "; prerr_exp exp; prerr_newline ();
        exit {temp} (1)
      end // end of [_]
  end // end of [auxexp]
  
  and auxarglst
    (res: &instrlst_vt, es: explst)
    : @(templst_vt, templst_vt) = let
    val narg = list_length (es)
    val nWORDSIZE = narg * WORDSIZE
    val tmps_rev = loop
      (res, $FRM.theFunargReglst, narg, list_vt_nil ()) where {
      fun loop (
          res: &instrlst_vt
        , fars: templst, n: int
        , tmps: templst_vt
        ) : templst_vt =
        if n > 0 then begin case+ fars of
          | list_cons (far, fars) => let
              val d0 = $TL.temp_make_new ()
              val () = emit
                (res, $ASM.INSTRmove (asm, src, dst)) where {
                val asm = "movl `s0, `d0"; val src = far and dst = d0
              } // end of [val]
            in
              loop (res, fars, n-1, list_vt_cons (d0, tmps))
            end // end of [list_cons]
          | list_nil () => tmps
        end else begin
          tmps // no more arguments and loop exits
        end // end of [if]
      // end of [loop]
    } // end of [val]
    val tmps = list_vt_reverse tmps_rev
    val () = emit
      (res, $ASM.INSTRoper (asm, src, dst, jump)) where {
      val asm = sprintf ("subl $%i, `s0", @(nWORDSIZE))
      val s0 = $FRM.SP; val src = '[s0] and dst = '[s0]; val jump = None ()
    } // end of [val]
    val ss_arg_rev = loop
      (res, es, $FRM.theFunargReglst, 0(*ofs*), list_vt_nil) where {
      fun loop (
          res: &instrlst_vt, es: explst, fars: templst, ofs: int, ss: templst_vt
        ) : templst_vt =
        case+ es of
        | list_cons (e, es) => let
            val s0 = auxexp (res, e); val ss = list_vt_cons (s0, ss)
          in
            case+ fars of
            | list_cons (far, fars) => let
                val () = emit
                  (res, $ASM.INSTRmove (asm, src, dst)) where {
                  val asm = "movl `s0, `d0"; val src = s0 and dst = far
                } // end of [val]
              in
                loop (res, es, fars, ofs + WORDSIZE, ss)
              end // end of [list_cons]
            | list_nil () => let
                val () = emit
                  (res, $ASM.INSTRoper (asm, src, dst, jump)) where  {
                  val asm = sprintf ("movl `s0, %i(`s1)", @(ofs));
                  val src = '[s0, $FRM.SP] and dst = '[]; val jump = None ()
                } // end of [val]
              in
                loop (res, es, fars, ofs + WORDSIZE, ss)
              end // end of [val]
          end // end of [list_cons]
        | list_nil () => ss
      // end of [loop]
    } // end of [val]
    val ss_arg = list_vt_reverse (ss_arg_rev)
  in
    @(tmps, ss_arg)
  end // end of [auxarglst]
in
  auxstm (res, stm)
end // end of [instrlst_add_stm]

(* ****** ****** *)

(* end of [codegen_x86_32.dats] *)
