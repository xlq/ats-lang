(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "error.sats"
staload "types.sats"
staload "absyn.sats"
staload "parser.sats"
staload "tychecker.sats"
staload INT0 = "interp0.sats"
staload TL = "templab.sats"
staload TR = "irtree.sats"
staload F = "frame.sats"
staload TRAN = "translate.sats"
staload CA = "canonical.sats"
staload INT1 = "interp1.sats"

staload "assem.sats"
staload "codegen.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"

(* ****** ****** *)

dynload "error.dats"
dynload "stamp.dats"
dynload "symbol.dats"
dynload "types.dats"
dynload "absyn.dats"

dynload "fixity.dats"
dynload "parser.dats"

dynload "PARCOMB/posloc.dats"
dynload "PARCOMB/tokenize.dats"
dynload "PARCOMB/parcomb.dats"

dynload "tychecker.dats"

dynload "interp0.dats"

dynload "templab.dats"

dynload "irtree.dats"

dynload "frame.dats"

dynload "translate.dats"

dynload "canonical.dats"

dynload "interp1.dats"

dynload "assem.dats"

dynload "codegen.dats"

(* ****** ****** *)

fn compusage (cmd: string) = begin
  printf ("%s --help: print out usage\n", @(cmd));
  printf ("%s --test: test a set of selected examples\n", @(cmd));
  printf ("%s <file>: compile the given <file>\n", @(cmd));
  printf ("%s : compile the program read from the stdin\n", @(cmd));
end // end of [compusage]

(* ****** ****** *)

fn comptest () = let
  val dirname = "Examples/TestCases"
  fn test (filename: string) = try let
    val exp = parse_from_file (filename)
    val () = printf
      ("The file [%s] is parsed successfully.", @(filename))
    val () = print_newline ()
    val ty = transProg (exp)
    val () = begin
      print "ty = "; print_ty (ty); print_newline ()
    end // end of [val]
(*
    val vlu = $INT0.interp0Prog (exp)
    val () = begin
      print "vlu = "; $INT0.print_value (vlu); print_newline ()
    end // end of [val]
*)
  in
    printf (
      "The file [%s] passed the test.\n", @(filename)
    ) // end of [printf]
  end with
    | ~FatalError _ => begin prerrf
        ("The file [%s] failed the test.\n", @(filename))     
      end
  // end of [test]
  val NFILE = 48 // [test49.tig] contains error
  val () = loop (1) where {
    fun loop (i: int): void =
      if i <= NFILE then let
        val filename = sprintf ("%s/test%i.tig", @(dirname, i))
        val () = test (filename)
      in
        loop (i + 1)
      end // end of [if]
    // end of [loop]
  } // end of [val]
  val ()  = test (dirname + "/merge.tig")
  val ()  = test (dirname + "/queens.tig")
in
  // empty
end // end of [comptest]

(* ****** ****** *)

fun print_stmlst (ss: $TR.stmlst): void =
  case+ ss of
  | list_cons (s, ss) => begin
      $TR.print_stm s; print_newline (); print_stmlst (ss)
    end // end of [list_cons]
  | list_nil () => print_newline ()
// end of [print_stmlst]

(* ****** ****** *)

implement main (argc, argv) = let
  val () = case+ argc of
    | _ when argc >= 2 => begin
      case+ argv.[1] of
      | "--help" => (
          compusage (argv.[0]); exit {void} (0)
        ) // end [--help]
      | "--test" => (comptest (); exit {void} (0))
      | _ => () // continue
      end // end of [_ when ...]
    | _ => ()
  // end of [val]
  val prog_exp = case+ argc of
    | 1 => parse_from_stdin ()
    | _ (* argc >= 2 *) =>> parse_from_file (argv.[1])
  // end of [val]
  val () = begin
    print "prog_exp = "; print_exp (prog_exp); print_newline ()
  end // end of [val]
  val prog_ty = transProg (prog_exp)
  val () = begin
    print "prog_ty = "; print_ty (prog_ty); print_newline ()
  end // end of [val]
(*
  val prog_vlu = $INT0.interp0Prog (prog_exp)
  val () = begin
    print "prog_vlu = "; $INT0.print_value (prog_vlu); print_newline ()
  end // end of [val]
*)

  val prog_e1xp = $TRAN.transProg1 (prog_exp)
  val () = begin
    print "prog_e1xp = "; $TRAN.print_e1xp prog_e1xp; print_newline ()
  end // end of [val]
  val prog_stm = $TRAN.unNx (prog_e1xp)
  val () = begin
    print "prog_stm = "; $TR.print_stm prog_stm; print_newline ()
  end // end of [val]
  
  val theFraglst = list_reverse ($F.frame_theFraglst_get ())
  
  datatype f1rag =
    | F1RAGproc of ($F.frame_t, $TR.stmlst) | F1RAGstring of ($TL.label_t, string)
  // end of [frag]
  typedef f1raglst = List f1rag

  val theF1raglst = loop (theFraglst, list_nil) where {
    fun loop (xs: $F.fraglst, res: f1raglst): f1raglst = case+ xs of
      | list_cons (x, xs) => let
          val f1rag = case+ x of
          | $F.FRAGproc (frm, stm) => let
              val stms = $CA.linearize stm
              val (lab_done, blks) = $CA.blocklst_gen (stms)
              val stms = $CA.trace_schedule (lab_done, blks)
              val lab_frm = $F.frame_name_get (frm)
              val () = $INT1.the_labmap_frame_stmlst_insert (lab_frm, frm, stms)
// (*
              val () = begin
                print "FRAGproc: "; $TL.print_label lab_frm; print_string ":\n";
                print_stmlst stms
              end // end of [val]
// *)
            in
              F1RAGproc (frm, stms)
            end // end of [FRAGproc]
          | $F.FRAGstring (lab, str) => let
              val () = $INT1.the_labmap_string_insert (lab, str)
// (*
              val () = begin
                print "FRAGstring: "; $TL.print_label lab; print_string ": ";
                print_string str; print_newline ()
              end // end of [val]
// *)
            in
              F1RAGstring (lab, str)
            end // end of [val]
        in
          loop (xs, list_cons (f1rag, res))
        end // end of [list_cons]
      | list_nil () => list_reverse (res)
    // end of [loop]
  } // end of [val]

  val prog_stms = $CA.linearize prog_stm
  val (lab_done, prog_blks) = $CA.blocklst_gen (prog_stms)
  val prog_stms = $CA.trace_schedule (lab_done, prog_blks)
  val () = print_stmlst prog_stms
// (*
  val () = $INT1.interp1Prog (prog_stms)
// *)

  val () = loop (theF1raglst) where {
    fun loop (xs: f1raglst): void = case+ xs of
      | list_cons (x, xs) => let
          val () = case+ x of
            | F1RAGproc (frm, stms) => let
                val lab_frm = $F.frame_name_get (frm)
                val () = begin
                  print "F1RAGproc: "; $TL.print_label lab_frm; print_string ":\n"
                end // end of [val]
                val inss = codegen_proc (frm, stms)
                val () = print_instrlst (inss)
              in
                // empty
              end // end of [val]
            | F1RAGstring (label, str) => ()
          // end of [val]
        in
          loop (xs)
        end // end of [list_cons]
      | list_nil () => ()
    // end of [loop]
  } // end of [val]

// (*
  val prog_inss = codegen_stmlst ($F.theTopFrame, prog_stms)
  val () = print_instrlst (prog_inss)
// *)
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [tiger_main.dats] *)
