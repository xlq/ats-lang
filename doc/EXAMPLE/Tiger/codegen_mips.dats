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
viewtypedef templst_vt = List_vt (temp)

(* ****** ****** *)

staload F = "frame.sats"
typedef frame = $F.frame_t

staload AS = "assem.sats"

(* ****** ****** *)

staload "irtree.sats"

(* ****** ****** *)

staload "codegen.sats"

(* ****** ****** *)

val theCallDefReglst = (
  $F.theSpecialReglst + $F.theCallersavedReglst
) : List temp

(* ****** ****** *)

val WORDSIZE = $F.WORDSIZE_get ()

viewtypedef instrlst_vt = List_vt ($AS.instr)

fn instrlst_add_stm
  (frm: frame, res: &instrlst_vt, stm: stm): void = let
  typedef instr = $AS.instr
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
        emit (res, $AS.INSTRoper (asm, src, dst, jump))
      end // end of [STMmove (EXPmem, _)]
    | STMmove (EXPtemp d0, e2) => let
        val s0 = auxexp (res, e2)
        val asm = "move `d0, `s0" // "addiu `d0, `s0, 0"
        val src = s0 and dst = d0
      in
        emit (res, $AS.INSTRmove (asm, src, dst))
      end // end of [STMmove (EXPtemp, _)]
    | STMjump (e, labs) => begin case+ e of
      | EXPname lab => let
          val asm = "j " + $TL.label_name_get lab
          val src = '[] and dst = '[]; val jump = Some '[lab]
        in
          emit (res, $AS.INSTRoper (asm, src, dst, jump))
        end // end of [EXPname]
      | _ => let
          val s0 = auxexp (res, e)
          val asm = "jr `s0"
          val src = '[s0] and dst = '[]; val jump = Some labs
        in
          emit (res, $AS.INSTRoper (asm, src, dst, jump))
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
        emit (res, $AS.INSTRoper (asm, src, dst, jump))
      end // end of [STMcjump]
    | STMlabel lab => let
        val asm = $TL.label_name_get (lab) + ":"
      in
        emit (res, $AS.INSTRlabel (asm, lab))
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
        emit (res, $AS.INSTRoper (asm, src, dst, jump)); d0        
      end // end of [EXPconst]
    | EXPname lab => let
        val d0 = $TL.temp_make_new ()
        val asm = "la `d0, " + $TL.label_name_get (lab)
        val src = '[] and dst = '[d0]; val jump = None ()
      in
        emit (res, $AS.INSTRoper (asm, src, dst, jump)); d0        
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
        emit (res, $AS.INSTRoper (asm, src, dst, jump)); d0
      end // end of [EXPbinop]
    | EXPmem (e) => let
        val s0 = auxexp (res, e)
        val d0 = $TL.temp_make_new ()
        val asm = "lw `d0, 0(`s0)"
        val src = '[s0] and dst = '[d0]; val jump = None ()
      in
        emit (res, $AS.INSTRoper (asm, src, dst, jump)); d0
      end // end of [EXPmem]
    | EXPcall (e_fun, es_arg) => let
        val tmpsfars = (case+ e_fun of
        | EXPname lab_fun => let
            val tmpsfars = auxarglst (res, es_arg)
            val () = emit
              (res, $AS.INSTRoper (asm, src, dst, jump)) where {
              val name = $TL.label_name_get (lab_fun)
              val asm = sprintf ("call .%s", @(name))
              val src = tmpsfars.1 and dst = '[]; val jump = None ()
            } // end of [val]
          in
            tmpsfars
          end // end of [_]
        | _ => let
            val s_fun = auxexp (res, e_fun)
            val tmpsfars = auxarglst (res, es_arg)
            val () = emit
              (res, $AS.INSTRoper (asm, src, dst, jump)) where {
              val asm = "call `s0"
              val src = list_cons (s_fun, tmpsfars.1) and dst = '[]
              val jump = None ()
            } // end of [val]
          in
            tmpsfars
          end // end of [_]
        ) : @(templst, templst) // end of [val]
        val () = loop
          (res, tmpsfars.0, tmpsfars.1) where {
          fun loop (
            res: &instrlst_vt, tmps: templst, fars: templst
            ) : void = case+ (tmps, fars) of
            | (list_cons (tmp, tmps), list_cons (far, fars)) => let
                val () = emit
                  (res, $AS.INSTRmove (asm, src, dst)) where {
                  val asm = "move `d0, `s0"; val src = tmp and dst = far
                } // end of [val]
              in
                loop (res, tmps, fars)
              end // end of [list_cons, list_cons]
            | (_, _) => ()
          // end of [loop]
        } // end of [val]
      in
        $F.RV
      end // end of [EXPcall]
    | _ => begin
        prerr "INTERNAL ERROR";
        prerr "auxexp: exp = "; prerr_exp exp; prerr_newline ();
        exit {temp} (1)
      end // end of [_]
  end // end of [auxexp]
  
  and auxarglst
    (res: &instrlst_vt, es: explst): @(templst, templst) = let
    val narg = list_length (es)
    val nWORDSIZE = narg * WORDSIZE
    val tmpsfars = loop (
        res
      , $F.theFunargReglst, narg
      , list_vt_nil, list_vt_nil
      ) where {
      fun loop (
          res: &instrlst_vt, fars: templst, n: int
        , res_tmps: templst_vt, res_fars: templst_vt
        ) : @(templst, templst) =
        if n > 0 then begin case+ fars of
          | list_cons (far, fars) => let
              val d0 = $TL.temp_make_new ()
              val () = emit
                (res, $AS.INSTRmove (asm, src, dst)) where {
                val asm = "move `d0, `s0"; val src = far and dst = d0
              } // end of [val]
              val res_tmps = list_vt_cons (d0, res_tmps)
              val res_fars = list_vt_cons (far, res_fars)
            in
              loop (res, fars, n-1, res_tmps, res_fars)
            end // end of [list_cons]
          | list_nil () => let
              val tmps = list_of_list_vt (list_vt_reverse res_tmps)
              val fars = list_of_list_vt (list_vt_reverse res_fars) in
              @(tmps, fars)
            end  // end of [list_nil]
        end else let
          val tmps = list_of_list_vt (list_vt_reverse res_tmps)
          val fars = list_of_list_vt (list_vt_reverse res_fars) in
          @(tmps, fars) // no more arguments and loop exits
        end // end of [if]
      // end of [loop]
    } // end of [val]
    val () = emit
      (res, $AS.INSTRoper (asm, src, dst, jump)) where {
      val asm = sprintf ("sub $%i, `s0", @(nWORDSIZE))
      val s0 = $F.SP; val src = '[s0] and dst = '[s0]; val jump = None ()
    } // end of [val]
    val () = loop (res, es, tmpsfars.1, 0(*ofs*)) where {
      fun loop
        (res: &instrlst_vt, es: explst, fars: templst, ofs: int): void =
        case+ es of
        | list_cons (e, es) => let
            val s0 = auxexp (res, e) in
            case+ fars of
            | list_cons (far, fars) => let
                val () = emit
                  (res, $AS.INSTRmove (asm, src, dst)) where {
                  val asm = "move `d0, `s0"; val src = s0 and dst = far
                } // end of [val]
              in
                loop (res, es, fars, ofs + WORDSIZE)
              end // end of [list_cons]
            | list_nil () => let
                val () = emit
                  (res, $AS.INSTRoper (asm, src, dst, jump)) where  {
                  val asm = sprintf ("sw `s0, %i(`s1)", @(ofs));
                  val src = '[s0, $F.SP] and dst = '[]; val jump = None ()
                } // end of [val]
              in
                loop (res, es, fars, ofs + WORDSIZE)
              end // end of [val]
          end // end of [list_cons]
        | list_nil () => ()
      // end of [loop]
    } // end of [val]
  in
    tmpsfars
  end // end of [auxarglst]
in
  auxstm (res, stm)
end // end of [instrlst_add_stm]

(* ****** ****** *)

(* end of [codegen_mips.dats] *)
