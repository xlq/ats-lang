(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload AS = "assem.sats"
typedef instrlst = $AS.instrlst

staload TL = "templab.sats"
typedef temp_t = $TL.temp_t
typedef label_t = $TL.label_t

(* ****** ****** *)

staload "fgnode.sats"
staload "tempset.sats"
staload "fgraph.sats"

(* ****** ****** *)

staload LM = "LIB/linmap_randbst.dats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"

(* ****** ****** *)

val _cmp_lab = lam
  (l1: label_t, l2: label_t): Sgn =<cloref>
  $TL.compare_label_label (l1, l2)
// end of [val]

implement fgraph_make_instrlst (inss) = let
  val asz = list_length (inss)
  val fg = fgraph_make_elt (asz, __elt) where {
    val __elt = $extval (fgnodeinfo_t, "(ats_ptr_type)0")
  } // end of [val]
  viewtypedef labmap_vt = $LM.map_vt (label_t, fgnode_t)
  var labmap: labmap_vt = $LM.linmap_empty ()
  val () = loop_vertex (fg, labmap, inss, 0) where {
    fun loop_vertex {n:nat} (
        fg: fgraph_t, labmap: &labmap_vt, inss: instrlst, n: int n
      ) : void = begin case+ inss of 
      | list_cons _ => let
          val fgn = fgnode_make_int (n)
          val+ list_cons (ins, inss) = inss
          val uselst = $AS.instr_uselst_get (ins)
          val deflst = $AS.instr_deflst_get (ins)
          val info = fgnodeinfo_make (fgn, uselst, deflst)
          val () = fgraph_nodeinfo_set (fg, fgn, info)
          val () = case+ ins of
          | $AS.INSTRlabel (_(*asm*), lab) => () where {
              val ans = begin
                $LM.linmap_insert<label_t,fgnode_t> (labmap, lab, fgn, _cmp_lab)
              end // end of [val]
              val () = begin
                case+ ans of | ~Some_vt _ => () | ~None_vt _ => ()
              end // end of [val]
            } // end of [INSTRlabel]
          | _ => ()
        in
          loop_vertex (fg, labmap, inss, n+1)
        end // end of [list_cons]
      | list_nil () => ()
    end // end of [loop_vertex]
  } // end of [val]
  val () = loop_edge (fg, labmap, inss, 0) where {
    fun loop_edge {n:nat} (
        fg: fgraph_t, labmap: !labmap_vt, inss: instrlst, n: int n
      ) : void = begin case+ inss of
      | list_cons (ins, inss) => let
          val fgn_fr = fgnode_make_int (n)
          val jump = $AS.instr_jump_get (ins)
          val () = case+ jump of
          | Some labs => let
              fun loop_labs (
                  fg: fgraph_t
                , labmap: !labmap_vt
                , fgn_fr: fgnode_t
                , labs: $TL.lablst
                ) : void = case+ labs of
                | list_cons (lab, labs) => let
                    val ans = $LM.linmap_search (labmap, lab, _cmp_lab)
                    val () = case+ ans of
                    | ~Some_vt fgn_to => fgraph_edge_insert (fg, fgn_fr, fgn_to)
                    | ~None_vt () => ()
                  in
                    loop_labs (fg, labmap, fgn_fr, labs)
                  end // end of [list_cons]
                | list_nil () => ()
              // end of [loop_labs]
            in
              loop_labs (fg, labmap, fgn_fr, labs)
            end // end of [Some]
          | None () => begin case+ inss of
            | list_cons _ => let
                val fgn_to = fgnode_make_int (n+1)
              in
                fgraph_edge_insert (fg, fgn_fr, fgn_to)
              end // end of [list_cons]
            | list_nil () => ()
            end (* end of [None] *)
        in
          loop_edge (fg, labmap, inss, n+1)
        end // end of [list_cons]
      | list_nil () => ()
    end (* end of [loop_edge] *)
  } // end of [val]
  val () = $LM.linmap_free (labmap)
in
  fg
end // end of [fgraph_make_instrlst]

(* ****** ****** *)

(*
**
** in[n]  = use[n] + (out[n] - def[n])
** out[n] = U (in[s]) where s ranges over succ[n]
**
*)

fn fgraph_outset_compute (fg: fgraph_t) =

(* ****** ****** *)

(* end of [liveness.dats] *)
