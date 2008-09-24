(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS/Anairiats - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
 * Free Software Foundation; either version 3, or (at  your  option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

// Time: March 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"
staload Fil = "ats_filename.sats"
staload Glo = "ats_global.sats"
staload IntInf = "ats_intinf.sats"
staload Lab = "ats_label.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"
staload "ats_ccomp.sats"
staload "ats_ccomp_env.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

extern fun emit_identifier {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, name: string): void
  = "ats_ccomp_emit_identifier"

%{$

ats_void_type
ats_ccomp_emit_identifier (ats_ptr_type out, ats_ptr_type name) {
  char c, *s ;

  s = name ;

  while (c = *s++) {
    if (isalnum (c)) {
      fputc (c, (FILE*)out) ; continue ;
    }
    if (c == '_' || c == '$') {
      fputc (c, (FILE*)out) ; continue ;
    }
    fputc ('_', (FILE*)out);
    fprintf ((FILE*)out, "%.2x", (unsigned char)c);
  } /* end of [while] */

  return ;
} /* ats_ccomp_emit_identifier */

%}

(* ****** ****** *)

implement emit_label (pf | out, l) =
  $Lab.fprint_label (pf | out, l)

(* ****** ****** *)

(*

implement emit_filename (pf | out, fil) =
  emit_identifier (pf | out, $Fil.filename_full fil)

*)

%{$

extern char *ats_main_ATSHOME ;
extern int ats_main_ATSHOME_length ;
extern char *ats_main_ATSHOMERELOC ;
extern ats_ptr_type ats_filename_full (ats_ptr_type) ;

ats_void_type
ats_ccomp_emit_filename (ats_ptr_type out, ats_ptr_type fil) {
  int sgn ; char *name ;
  name = ats_filename_full (fil) ;

  if (!ats_main_ATSHOMERELOC) {
    ats_ccomp_emit_identifier (out, name) ; return ;
  }

  sgn = strncmp
    (ats_main_ATSHOME, name, ats_main_ATSHOME_length) ;
  if (sgn) {
    ats_ccomp_emit_identifier (out, name) ;
  } else {
    ats_ccomp_emit_identifier (out, ats_main_ATSHOMERELOC) ;
    ats_ccomp_emit_identifier (out, (char*)name + ats_main_ATSHOME_length) ;
  }

  return ;
} /* end of ats_ccomp_emit_filename */

%}

(* ****** ****** *)

implement emit_d2con (pf | out, d2c) = let
  val fil = d2con_fil_get d2c
  val name = $Sym.symbol_name (d2con_sym_get d2c)
  val () = emit_filename (pf | out, fil)
  val () = fprint (pf | out, "__")
in
  emit_identifier (pf | out, name)
end // end of [emit_d2con]

implement emit_d2cst (pf | out, d2c) = let
  val ext = d2cst_ext_get (d2c)
in
  if stropt_is_none ext then let
    val fil = d2cst_fil_get (d2c)
    val name = $Sym.symbol_name (d2cst_sym_get d2c)
    val () = emit_filename (pf | out, fil)
    val () = fprint (pf | out, "__")
    val () = emit_identifier (pf | out, name)
  in
    // empty
  end else begin
    emit_identifier (pf | out, stropt_unsome ext)
  end
end // end of [emit_d2cst]

fn emit_funlab_prefix {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m)
  : void = let
  val prfx = $Glo.ats_function_name_prefix_get ()
in
  if stropt_is_some prfx then begin
    let val prfx = stropt_unsome prfx in fprint (pf | out, prfx) end
  end else begin
    // the default is the empty string
  end
end // end of [emit_funlab_prefix]

implement emit_funlab (pf | out, fl) = begin
  case+ funlab_qua_get fl of
  | D2CSTOPTsome d2c => let // global function
      val () = emit_d2cst (pf | out, d2c)
    in
      case+ d2cst_kind_get d2c of
      | $Syn.DCSTKINDval () => fprint (pf | out, "$fun") | _ => ()
    end // end of [D2CSTOPTsome]
  | D2CSTOPTnone () => let // local function
      val () = emit_funlab_prefix (pf | out)
      val () = emit_identifier (pf | out, funlab_name_get fl)
    in
      // empty
    end // end of [D2CSTOPTnone]
end // end of [emit_funlab]

implement emit_tmplab (pf | out, tl) = begin
  fprint (pf | out, "__ats_lab_");
  $Stamp.fprint_stamp (pf | out, tmplab_stamp_get tl)
end

implement emit_tmplabint (pf | out, tl, i) = begin
  emit_tmplab (pf | out, tl); fprintf (pf | out, "_%i", @(i))
end

implement emit_tmpvar (pf | out, tmp) = begin
  fprint (pf | out, "tmp");
  $Stamp.fprint_stamp (pf | out, tmpvar_stamp_get tmp)
end

(* ****** ****** *)

#define PTR_TYPE_NAME "ats_ptr_type"

fn _emit_hityp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, hit: hityp)
  : void = let
  val HITNAM (knd, name) = hit.hityp_name
  val () = if knd = 0 then fprint_string (pf | out, name)
  val () = if knd > 0 then fprint (pf | out, PTR_TYPE_NAME)
in
  // empty
end // end of [_emit_hityp]

implement emit_hityp (pf | out, hit) =
  _emit_hityp (pf | out, hityp_decode hit)

fn _emit_hityplst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, hits: hityplst)
  : void = let
  fun aux (out: &FILE m, i: int, hits: hityplst)
    : void = begin case+ hits of
    | list_cons (hit, hits) => begin
        if i > 0 then fprint (pf | out, ", ");
        _emit_hityp (pf | out, hit); aux (out, i+1, hits)
      end
    | list_nil () => ()
  end // end of [aux]
in
  aux (out, 0, hits)
end // end of [emit_hityplst]

implement emit_hityplst {m} (pf | out, hits) =
  _emit_hityplst (pf | out, hityplst_decode hits)

(* ****** ****** *)

fn _emit_hityp_ptr {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, hit: hityp)
  : void = let
  val HITNAM (knd, name) = hit.hityp_name
  val () = fprint_string (pf | out, name)
  val () = if knd = 0 then fprint (pf | out, '&') // an error!
in
  // empty
end // end of [emit_hityp_ptr]

implement emit_hityp_ptr (pf | out, hit) =
  _emit_hityp_ptr (pf | out, hityp_decode hit)

(* ****** ****** *)

extern fun emit_hityp_fun {m:file_mode} (
  pf: file_mode_lte (m, w) | out: &FILE m, hits_arg: hityplst_t, hit_res: hityp_t
) : void

extern fun emit_hityp_clofun {m:file_mode} (
  pf: file_mode_lte (m, w) | out: &FILE m, hits_arg: hityplst_t, hit_res: hityp_t
) : void

implement emit_hityp_fun (pf | out, hits_arg, hit_res) = begin
  emit_hityp (pf | out, hit_res);
  fprint (pf | out, "(*)(");
  emit_hityplst (pf | out, hits_arg);
  fprint (pf | out, ")")
end // end of [emit_hityp_fun]

implement emit_hityp_clofun (pf | out, hits_arg, hit_res) = let
  val () = emit_hityp (pf | out, hit_res)
  val () = fprint (pf | out, "(*)(ats_clo_ptr_type")
  val () = case+ 0 of
    | _ when hityplst_is_cons hits_arg => begin
        fprint (pf | out, ", "); emit_hityplst (pf | out, hits_arg)
      end
    | _ => ()
  val () = fprint (pf | out, ")")
in
  // empty
end // end of [emit_hityp_fun]

(* ****** ****** *)

extern fun emit_cloenv {m:file_mode} (
  pf: file_mode_lte (m, w) | out: &FILE m, map: envmap_t, vtps: vartypset
) : int

(* ****** ****** *)

local

viewtypedef valprimlstlst_vt = List_vt (valprimlst)

val the_level = ref_make_elt<int> (0)
val the_funarglst = ref_make_elt<valprimlst> (list_nil ())
val the_funarglstlst = ref_make_elt<valprimlstlst_vt> (list_vt_nil ())

in

fn funarglst_find (i: int): Option_vt (valprim) = let
  fun aux (vps: valprimlst, i: int): valprim = begin
    case+ vps of
    | list_cons (vp, vps) => if i > 0 then aux (vps, i-1) else vp
    | list_nil () => valprim_void () // deadcode
  end // end of [aux]
in
  if !the_level > 0 then Some_vt (aux (!the_funarglst, i)) else None_vt ()
end // end of [funarglst_find]

fn funarglst_pop (): void = let
  val n = !the_level
  val () = // run-time checking
    if n > 0 then (!the_level := n - 1) else begin
      prerr "Internal Error: ats_ccomp_emit: funarglst_pop: 1";
      prerr_newline ()
    end
  var vps0: valprimlst = list_nil ()
  val () = let
    val (vbox pf | p) = ref_get_view_ptr (the_funarglstlst)
  in
    case+ !p of
    | ~list_vt_cons (vps, vpss) => begin
        !p := (vpss: valprimlstlst_vt); vps0 := vps
      end
    | list_vt_nil () => fold@ (!p)
  end
in
  !the_funarglst := vps0
end // end of [funarglst_pop]

fn funarglst_push (vps: valprimlst): void = let
  val n = !the_level; val () = !the_level := n + 1
in
  if n > 0 then let
    val vps0 = !the_funarglst
    val () = (!the_funarglst := vps)
    val (vbox pf | p) = ref_get_view_ptr (the_funarglstlst)
  in
    !p := list_vt_cons (vps0, !p)
  end else begin
    !the_funarglst := vps
  end
end // end of [funarglst_push]

end // end of [local]

(* ****** ****** *)

fn emit_valprim_arg {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, ind: int)
  : void = begin case+ funarglst_find ind of
  | ~Some_vt vp => emit_valprim (pf | out, vp)
  | ~None_vt () => begin
      fprint (pf | out, "arg"); fprint_int (pf | out, ind)
    end
end // end of [emit_valprim_arg]

fn emit_valprim_arg_ref {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, ind: int, hit: hityp_t)
  : void = begin case+ funarglst_find ind of
  | ~Some_vt vp => begin
      fprint (pf | out, "*((");
      emit_hityp (pf | out, hit);
      fprint (pf | out, "*)");
      emit_valprim (pf | out, vp);
      fprint (pf | out, ")")
    end
  | ~None_vt () => begin
      fprint (pf | out, "*((");
      emit_hityp (pf | out, hit);
      fprint (pf | out, "*)arg");
      fprint_int (pf | out, ind);
      fprint (pf | out, ")")
    end
end // end of [emit_valprim_arg_ref]

(* ****** ****** *)

fn emit_valprim_bool {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, b: bool)
  : void = begin
  if b then begin
    fprint (pf | out, "ats_true_bool")
  end else begin
    fprint (pf | out, "ats_false_bool")
  end
end // end of [emit_valprim_bool]

fn emit_valprim_char {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, c: char)
  : void = begin case+ c of
  | '\'' => fprint (pf | out, "'\\''")
  | '\n' => fprint (pf | out, "'\\n'")
  | '\t' => fprint (pf | out, "'\\t'")
  | '\\' => fprint (pf | out, "'\\\\'")
  | _ when char_isprint c => fprintf (pf | out, "'%c'", @(c))
  | _ => fprintf (pf | out, "'\\%.3o'", @(uint_of_char c))
end

fn emit_valprim_clo {m:file_mode} (
    pf: file_mode_lte (m, w)
  | out: &FILE m, knd: int, fl: funlab_t, map: envmap_t
  ) : void = let
  val entry = funlab_entry_get_some (fl)
  val vtps = funentry_vtps_get_all (entry)
  val () = emit_funlab (pf | out, fl)
  val () = fprint (pf | out, "_closure_make (")
  val _(*int*) = emit_cloenv (pf | out, map, vtps)
  val () = fprint (pf | out, ")")
in
  // empty
end // end of [emit_valprim_clo]

(* ****** ****** *)

extern fun emit_valprim_float {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, f: string): void
  = "ats_ccomp_emit_valprim_float"

%{$

ats_void_type
ats_ccomp_emit_valprim_float
  (ats_ptr_type out, ats_ptr_type f) {
  char *s = f ;
  if (*s == '~') { fputc ('-', (FILE*)out) ; s += 1 ; }
  fputs (s, (FILE*)out) ;
  return ;
} /* ats_ccomp_emit_valprim_float */

%}

(* ****** ****** *)

fn emit_valprim_int {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, int: intinf_t)
  : void = begin
  $IntInf.fprint_intinf (pf | out, int)
end // end of [emit_valprim_int]

(* ****** ****** *)

fn emit_valprim_ptrof {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, vp: valprim)
  : void = begin case+ vp.valprim_node of
  | VParg ind => begin
      fprint (pf | out, "(&");
      emit_valprim_arg (pf | out, ind);
      fprint (pf | out, ")")
    end
  | VParg_ref ind => emit_valprim_arg (pf | out, ind)
  | VPenv vtp => let
      val ind = varindmap_find_some (vartyp_var_get vtp)
    in
      fprint (pf | out, "env"); fprint_int (pf | out, ind)
    end
  | VPtmp_ref tmp => let
      val () = fprint (pf | out, "(&")
      val () = emit_tmpvar (pf | out, tmp)
      val () = fprint (pf | out, ")")
    in
      // empty
    end // end of [VPtmp]
  | _ => begin
      prerr "Internal Error: ats_ccomp_emit: emit_valprim_ptrof: vp = ";
      prerr_valprim vp;
      $Err.abort {void} ()
    end
end // end of [emit_valprim_ptrof]

(* ****** ****** *)

fn emit_select_lab {m:file_mode} (
    pf: file_mode_lte (m, w)| out: &FILE m, lab: lab_t
  ) : void = begin
  fprint (pf | out, ".atslab_"); emit_label (pf | out, lab)
end // end of [emit_select_lab]

fn emit_select_lab_ptr {m:file_mode} (
    pf: file_mode_lte (m, w)| out: &FILE m, lab: lab_t
  ) : void = begin
  fprint (pf | out, "->atslab_"); emit_label (pf | out, lab)
end // end of [emit_select_lab_ptr]

fn emit_array_index  {m:file_mode} (
    pf: file_mode_lte (m, w)
  | out: &FILE m, vpss: valprimlstlst
  ) : void = let
  fun aux (
      out: &FILE m, vpss: valprimlstlst
    ) : void = begin case+ vpss of
    | list_cons (vps, vpss) => begin
        fprint (pf | out, "[");
        emit_valprimlst (pf | out, vps);
        fprint (pf | out, "]");
        aux (out, vpss)
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [aux]
in
  aux (out, vpss)
end // end of [emit_array_index]

(* ****** ****** *)

fn emit_valprim_select_bef {m:file_mode} (
    pf: file_mode_lte (m, w) | out: &FILE m, offs: offsetlst
  ) : void = let
  fun aux (
      out: &FILE m , offs: offsetlst
    ) : void = begin case+ offs of
    | list_cons (off, offs) => begin
      case+ off of
      | OFFSETind (vpss, hit_elt) => begin
          fprint (pf | out, "((");
          emit_hityp (pf | out, hit_elt);
          fprint (pf | out, "*)");
          aux (out, offs)
        end // end of [OFFSETind]
      | OFFSETlab (lab, hit_rec) => let
          val hit_rec = hityp_decode (hit_rec)
          val HITNAM (knd, name) = hit_rec.hityp_name
          val () = fprint (pf | out, "(")
          val () =
            if knd > 0 (*ptr*) then begin
              fprint (pf | out, "(");
              fprint (pf | out, name);
              fprint (pf | out, "*)")
            end
        in
          aux (out, offs)
        end // end of [OFFSETlab]
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [aux]
in
  aux (out, offs)
end // end of [emit_valprim_select_bef]

(* ****** ****** *)

fn emit_valprim_select_aft {m:file_mode} (
    pf: file_mode_lte (m, w) | out: &FILE m, offs: offsetlst
  ) : void = let
  fun aux (out: &FILE m, offs: offsetlst)
    : void = begin case+ offs of
    | list_cons (off, offs) => begin case+ off of
      | OFFSETind (vpss, hit_elt) => begin
          fprint (pf | out, ")");
          emit_array_index (pf | out, vpss);
          aux (out, offs)
        end // end of [OFFSETind]
      | OFFSETlab (lab, hit_rec) => begin
        case+ 0 of
        | _ when hityp_t_is_tyrecbox hit_rec => let
            val () = fprint (pf | out, ")")
            val () = emit_select_lab_ptr (pf | out, lab)
          in
            aux (out, offs)
          end
        | _ when hityp_t_is_tyrecsin hit_rec => let
            val () = fprint (pf | out, ")")
          in
            aux (out, offs)
          end
        | _ => let
            val () = fprint (pf | out, ")")
            val () = emit_select_lab (pf | out, lab)
          in
            aux (out, offs)
          end
        end // end of [OFFSETlab]
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [aux]
in
  aux (out, offs)
end // end of [emit_valprim_select_aft]

(* ****** ****** *)

fn emit_valprim_select {m:file_mode} (
    pf: file_mode_lte (m, w)
  | out: &FILE m, vp_root: valprim, offs: offsetlst
  ) : void = let
  val () = emit_valprim_select_bef (pf | out, offs)
  val () = emit_valprim (pf | out, vp_root)
  val () = emit_valprim_select_aft (pf | out, offs)
in
  // empty
end // end of [emit_valprim_select]

(* ****** ****** *)

(* 0/1: var/ptr *)
fn emit_valprim_select_varptr {m:file_mode} (
    pf: file_mode_lte (m, w)
  | out: &FILE m, knd: int, vp_root: valprim, offs: offsetlst
  ) : void = let
  fn aux_fst (
      out: &FILE m, knd: int, vp_root: valprim, off: offset
    ) : void = begin case+ off of
    | OFFSETind (vpss, hit_elt) => begin
        fprint (pf | out, "((");
        emit_hityp (pf | out, hit_elt);
        fprint (pf | out, "*)");
        if knd > 0 then begin
          emit_valprim (pf | out, vp_root); // ptr
        end else begin
          emit_valprim_ptrof (pf | out, vp_root); // var
        end; // end of [if]
        fprint (pf | out, ")");
        emit_array_index (pf | out, vpss);
      end // end of [OFFSETind]
    | OFFSETlab (lab, hit_rec) => begin
      case+ 0 of
      | _ when hityp_t_is_tyrecbox hit_rec => let
          val () = fprint (pf | out, "((")
          val () = emit_hityp_ptr (pf | out, hit_rec)
          val () = fprint (pf | out, "*)")
          val () = emit_valprim (pf | out, vp_root)
          val () = fprint (pf | out, ")")
        in
          emit_select_lab_ptr (pf | out, lab)
        end
      | _ when hityp_t_is_tyrecsin hit_rec => let
          val () = fprint (pf | out, "(")
          val () = emit_hityp (pf | out, hit_rec)
          val () = if knd > 0 then fprint (pf | out, '*')
          val () = fprint (pf | out, ")")
        in
          emit_valprim (pf | out, vp_root)
        end
      | _ => let // [hit_rec] is flat!
          val () = fprint (pf | out, "(")
          val () = (case+ 0 of
            | _ when knd > 0 => let
                val () = fprint (pf | out, "(")
                val () = emit_hityp (pf | out, hit_rec)
                val () = fprint (pf | out, "*)")
              in
                // empty
              end // end of [_ when ...]
            | _ => ()
          ) // end of [val]
          val () = emit_valprim (pf | out, vp_root)
          val () = fprint (pf | out, ")")
        in
          case+ 0 of
          | _ when knd > 0 => begin
              emit_select_lab_ptr (pf | out, lab) // ptr
            end
          | _ => emit_select_lab (pf | out, lab) // var
        end
    end // end [OFFSETlab]
  end // end of [aux_fst]
in
  case+ offs of
  | list_cons (off_fst, offs_rst) => let
      val () = emit_valprim_select_bef (pf | out, offs_rst)
      val () = aux_fst (out, knd, vp_root, off_fst)
      val () = emit_valprim_select_aft (pf | out, offs_rst)
    in
      // empty
    end
  | list_nil () => begin
      prerr "Internal Error: ";
      prerr "ats_ccomp_emit: emit_valprim_select_varptr: vp_root = ";
      prerr vp_root; prerr_newline ();
      $Err.abort {void} ()
    end
end // end of [emit_valprim_select_varptr]

fn emit_valprim_select_var {m:file_mode} (
    pf: file_mode_lte (m, w)
  | out: &FILE m, vp_root: valprim, offs: offsetlst
  ) : void = begin
  emit_valprim_select_varptr (pf | out, 0(*var*), vp_root, offs)
end // end of [emit_valprim_select_var]

fn emit_valprim_select_ptr {m:file_mode} (
    pf: file_mode_lte (m, w)
  | out: &FILE m, vp_root: valprim, offs: offsetlst
  ) : void = begin
  emit_valprim_select_varptr (pf | out, 1(*ptr*), vp_root, offs)
end // end of [emit_valprim_select_ptr]

(* ****** ****** *)

extern fun emit_valprim_string {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, str: string, len: int): void
  = "ats_ccomp_emit_valprim_string"

%{$

ats_void_type ats_ccomp_emit_valprim_string 
  (ats_ptr_type out, ats_ptr_type str, ats_int_type len) {
  char *s, c; int i;

  fputc ('"', (FILE*)out);

  s = (char*)str ;
  for (i = 0; i < len; i += 1, s += 1) {
    c = *s;
    switch (c) {
    case '"': fprintf ((FILE*)out, "\\\""); break;
    case '\n': fprintf ((FILE*)out, "\\n"); break;
    case '\t': fprintf ((FILE*)out, "\\t"); break;
    case '\\': fprintf ((FILE*)out, "\\\\"); break;
    default:
      if (isprint(c)) {
        fputc (c, (FILE*)out) ;
      } else {
        fprintf ((FILE*)out, "\\%.3o", (unsigned char)c);
      }
    } // end of [switch]
  } // end of [for]

  fputc ('"', (FILE*)out);

} // end of [ats_ccomp_emit_valprim_string]

%}

(* ****** ****** *)

implement emit_valprim_tmpvar (pf | out, tmp) = let
  val tmp = (
    case+ tmpvar_root_get (tmp) of
    | TMPVAROPTsome tmp => tmp | TMPVAROPTnone () => tmp
  ) : tmpvar_t
in
  emit_tmpvar (pf | out, tmp)
end // end of [emit_valprim_tmpvar]

(* ****** ****** *)

implement emit_valprim (pf | out, vp) = begin
  case+ vp.valprim_node of
  | VParg ind => emit_valprim_arg (pf | out, ind)
  | VParg_ref ind => begin
      emit_valprim_arg_ref (pf | out, ind, vp.valprim_typ)
    end
  | VPbool b => emit_valprim_bool (pf | out, b)
  | VPchar c => emit_valprim_char (pf | out, c)
  | VPclo (knd, fl, env) => begin
      emit_valprim_clo (pf | out, knd, fl, env)
    end
  | VPcst d2c => begin case+ 0 of
    | _ when d2cst_is_fun d2c => begin
        fprint (pf | out, '&'); emit_d2cst (pf | out, d2c)
      end
    | _ => emit_d2cst (pf | out, d2c)
    end
  | VPenv vtp => let
      val d2v = vartyp_var_get vtp
      val ind = varindmap_find_some (d2v)
    in
      case+ 0 of
      | _ when d2var_is_mutable d2v => begin
          fprint (pf | out, "*(");
          emit_hityp (pf | out, vartyp_typ_get vtp);
          fprintf (pf | out, "*)env%i", @(ind))
        end
      | _ => begin
          fprintf (pf | out, "env%i", @(ind))
        end
    end // end of [VPenv]
  | VPext code => fprint (pf | out, code)
  | VPfloat f => emit_valprim_float (pf | out, f)
  | VPfun fl => begin
      fprint (pf | out, "&"); emit_funlab (pf | out, fl)
    end
  | VPint (int) =>
      $IntInf.fprint_intinf (pf | out, int)
  | VPintsp (str, _(*int*)) => fprint (pf | out, str)
  | VPptrof vp => emit_valprim_ptrof (pf | out, vp)
  | VPptrof_ptr_offs (vp, offs) => begin
      fprint (pf | out, '&'); emit_valprim_select_ptr (pf | out, vp, offs)
    end
  | VPptrof_var_offs (vp, offs) => begin
      fprint (pf | out, '&'); emit_valprim_select_var (pf | out, vp, offs)
    end
  | VPsizeof hit => let
      val () = fprint (pf | out, "sizeof(")
      val () = emit_hityp (pf | out, hit)
      val () = fprint (pf | out, ")")
    in
      // empty
    end // end of [VPsizeof]
  | VPstring (str, len) => emit_valprim_string (pf | out, str, len)
  | VPtmp tmp => emit_valprim_tmpvar (pf | out, tmp)
  | VPtmp_ref tmp => emit_valprim_tmpvar (pf | out, tmp)
  | VPtop () => fprint (pf | out, "?top") // for debugging
  | VPvoid () => fprint (pf | out, "?void") // for debugging
(*
  | _ => begin
      prerr "Internal Error: emit_valprim: vp = "; prerr vp; prerr_newline ();
      $Err.abort {void} ()
    end
*)
end // end of [emit_valprim]

implement emit_valprimlst {m} (pf | out, vps) = let
  fun aux (out: &FILE m, i: int, vps: valprimlst)
    : void = begin case+ vps of
    | list_cons (vp, vps) => begin
        if i > 0 then fprint (pf | out, ", ");
        emit_valprim (pf | out, vp); aux (out, i+1, vps)
      end
    | list_nil () => ()
  end // end of [aux]
in
  aux (out, 0, vps)
end // end of [emit_valprimlst]    

(* ****** ****** *)

implement emit_kont (pf | out, kont) = begin
  case+ kont of
  | KONTtmplab tl => begin
      fprint (pf | out, "goto ");
      emit_tmplab (pf | out, tl)
    end
  | KONTtmplabint (tl, i) => begin
      fprint (pf | out, "goto ");
      emit_tmplabint (pf | out, tl, i)
    end
  | KONTcaseof_fail () => begin
      fprint (pf | out, "ats_caseof_failure ()")
    end
  | KONTfunarg_fail fl => begin
      fprint (pf | out, "ats_funarg_failure ()")
    end
  | KONTraise vp_exn => begin
      fprint (pf | out, "ats_raise_exn (");
      emit_valprim (pf | out, vp_exn);
      fprint (pf | out, ")")
    end
  | KONTmatpnt mpt => emit_matpnt (pf | out, mpt)
  | KONTnone () => begin
      fprint (pf | out, "ats_deadcode_failure ()")
    end
end // end of [emit_kont]

(* ****** ****** *)

extern fun emit_patck {m:file_mode} (
  pf: file_mode_lte (m, w) | out: &FILE m, vp: valprim, patck: patck, fail: kont
) : void

implement emit_patck
  (pf | out, vp, patck, fail) = begin case+ patck of
  | PATCKbool b => begin
      fprint (pf | out, "if (");
      if b then fprint (pf | out, '!');
      emit_valprim (pf | out, vp);
      fprint (pf | out, ") { ");
      emit_kont (pf | out, fail);
      fprint (pf | out, " ; }")
    end
  | PATCKchar c => begin
      fprint (pf | out, "if (");
      emit_valprim (pf | out, vp);
      fprint (pf | out, " != ");
      emit_valprim_char (pf | out, c);
      fprint (pf | out, ") { ");
      emit_kont (pf | out, fail);
      fprint (pf | out, " ; }")
    end
  | PATCKcon d2c => let
      val s2c = d2con_scst_get (d2c)
    in
      case+ s2c of
      | _ when s2cst_is_singular (s2c) => ()
      | _ when s2cst_is_listlike (s2c) => let
          val isnil = (
            case+ s2cst_islst_get (s2c) of
            | Some x(*nil,cons*) => eq_d2con_d2con (d2c, x.0)
            | None () => false (* deadcode *)
          ) : bool
          val iscons = not (isnil)
        in
          fprint (pf | out, "if (");
          emit_valprim (pf | out, vp);
          if isnil then fprint (pf | out, " != ");
          if iscons then fprint (pf | out, " == ");
          fprint (pf | out, "(ats_sum_ptr_type)0) { ");
          emit_kont (pf | out, fail);
          fprint (pf | out, " ; }")
        end // end of [s2cst_is_listlike]
      | _ => begin
          fprint (pf | out, "if (((ats_sum_ptr_type)");
          emit_valprim (pf | out, vp);
          fprint (pf | out, ")->tag != ");
          fprint_int (pf | out, d2con_tag_get d2c);
          fprint (pf | out, ") { ");
          emit_kont (pf | out, fail);
          fprint (pf | out, " ; }")
        end
    end // end of [PATCKcon]
  | PATCKexn d2c => let
      val arity = d2con_arity_real_get d2c
    in
      case+ arity of
      | _ when arity = 0 => begin
          fprint (pf | out, "if (");
          emit_valprim (pf | out, vp);
          fprint (pf | out, " != &");
          emit_d2con (pf | out, d2c);
          fprint (pf | out, ") { ");
          emit_kont (pf | out, fail);
          fprint (pf | out, " ; }")
        end
      | _ => begin
          fprint (pf | out, "if (((ats_exn_ptr_type)");
          emit_valprim (pf | out, vp);
          fprint (pf | out, ")->tag != ");
          emit_d2con (pf | out, d2c);
          fprint (pf | out, ".tag) { ");
          emit_kont (pf | out, fail);
          fprint (pf | out, " ; }")
        end
    end // end of [PATCKexn]
  | PATCKfloat (f) => begin
      fprint (pf | out, "if (");
      emit_valprim (pf | out, vp);
      fprint (pf | out, " != ");
      emit_valprim_float (pf | out, f);
      fprint (pf | out, ") { ");
      emit_kont (pf | out, fail);
      fprint (pf | out, " ; }")
    end
  | PATCKint int => begin
      fprint (pf | out, "if (");
      emit_valprim (pf | out, vp);
      fprint (pf | out, " != ");
      emit_valprim_int (pf | out, int);
      fprint (pf | out, ") { ");
      emit_kont (pf | out, fail);
      fprint (pf | out, " ; }")
    end
  | PATCKstring str => begin
      fprint (pf | out, "if (strcmp(");
      emit_valprim (pf | out, vp);
      fprint (pf | out, ", ");
      emit_valprim_string (pf | out, str, length str);
      fprint (pf | out, ")) { ");
      emit_kont (pf | out, fail);
      fprint (pf | out, " ; }")
    end
(*
  | _ => begin
      prerr "Internal Error: emit_patck: not implemented yet";
      prerr_newline ();
      $Err.abort {void} ()
    end
*)
end // end of [emit_patck]

(* ****** ****** *)

extern fun emit_branch {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, br: branch): void

implement emit_branch (pf | out, br) = let
  val inss = br.branch_inss
  val () = fprint (pf | out, "/* branch: ")
  val () = emit_tmplab (pf | out, br.branch_lab)
  val () = fprint (pf | out, " */")
  val () = begin case+ inss of
    | list_cons _ => fprint (pf | out, '\n') | list_nil () => ()
  end
in
  emit_instrlst (pf | out, inss); fprint (pf | out, "\nbreak ;\n")
end // end of [emit_branch]

extern fun emit_branchlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, brs: branchlst): void

implement emit_branchlst {m} (pf | out, brs) = let
  fun aux (out: &FILE m, i: int, brs: branchlst): void =
    case+ brs of
    | list_cons (br, brs) => let
        val () = if i > 0 then fprint (pf | out, '\n')
      in
        emit_branch (pf | out, br); aux (out, i+1, brs)
      end
    | list_nil () => ()
in
  aux (out, 0, brs)
end // end of [emit_branchlst]

(* ****** ****** *)

implement emit_cloenv {m}
  (pf | out, map, vtps): int = let
  fn aux_envmap
    (out: &FILE m, map: envmap_t, d2v: d2var_t)
    : void = begin
    case+ envmap_find (map, d2v) of
    | ~Some_vt vp => let
        val () = begin
          if d2var_is_mutable d2v then fprint (pf | out, '&')
        end
      in
        emit_valprim (pf | out, vp)
      end
    | ~None_vt () => begin
        prerr "Internal Error";
        prerr ": ats_ccomp_emit: emit_cloenv";
        prerr ": the dynamic variable [";
        prerr d2v;
        prerr "] is not bound to a value.";
        prerr_newline ()
      end // end of [None_vt]
  end // end of [envmap]

  fun aux_main (
      out: &FILE m
    , map: envmap_t
    , i: int
    , d2vs: d2varlst_vt
    , err: &int
    ) :<cloptr1> int = begin
    case+ d2vs of
    | ~list_vt_cons (d2v, d2vs) => let
        val () = if i > 0 then fprint (pf | out, ", ")
        val () = begin case+ varindmap_find (d2v) of
          | ~Some_vt ind => fprintf (pf | out, "env%i", @(ind))
          | ~None_vt () => aux_envmap (out, map, d2v)
        end
      in
        aux_main (out, map, i+1, d2vs, err)
      end
    | ~list_vt_nil () => i
  end // end of [aux_main]

  val d2vs = vartypset_d2varlst_make (vtps)
  var err: int = 0
  val n = aux_main (out, map, 0, d2vs, err)
  val () = if err > 0 then $Err.abort {void} ()
in
  n // the number of variables in the closure environment
end // end of [emit_cloenv]

(* ****** ****** *)

fn emit_move_con {m:file_mode} (
    pf: file_mode_lte (m, w)
  | out: &FILE m
  , tmp: tmpvar_t
  , hit_sum: hityp_t
  , d2c: d2con_t
  , vps: valprimlst
  ) : void = begin case+ vps of
  | list_cons _ => let
      val () = emit_valprim_tmpvar (pf | out, tmp)
      val () = fprint (pf | out, " = ATS_MALLOC (sizeof(")
      val () = emit_hityp_ptr (pf | out, hit_sum)
      val () = fprint (pf | out, ")) ;")
      val () = (
        case+ 0 of
        | _ when d2con_is_exn (d2c) => begin
            fprint (pf | out, '\n');
            fprint (pf | out, "((ats_exn_ptr_type)");
            emit_valprim_tmpvar (pf | out, tmp);
            fprint (pf | out, ")->tag = ");
            emit_d2con (pf | out, d2c);
            fprint (pf | out, ".tag ;\n");
            fprint (pf | out, "((ats_exn_ptr_type)");
            emit_valprim_tmpvar (pf | out, tmp);
            fprint (pf | out, ")->name = ");
            emit_d2con (pf | out, d2c);
            fprint (pf | out, ".name ;")
          end
        | _ => let
            val s2c = d2con_scst_get d2c
          in
            case+ 0 of
            | _ when s2cst_is_singular s2c => ()
            | _ when s2cst_is_listlike s2c => ()
            | _ => begin
                fprint (pf | out, '\n');
                fprint (pf | out, "((ats_sum_ptr_type)");
                emit_valprim_tmpvar (pf | out, tmp);
                fprint (pf | out, ")->tag = ");
                fprint_int (pf | out, d2con_tag_get d2c);
                fprint (pf | out, " ;")
              end
          end // end of [_]
      ) // end of [val]
      val () = aux_arg (out, 0, vps) where {
        fun aux_arg (
            out: &FILE m
          , i: int
          , vps: valprimlst
          ) :<cloptr1> void = begin case+ vps of
          | list_cons (vp, vps) => let
              val () = begin case+ vp.valprim_node of
                | VPtop () => ()
                | _ => begin
                    fprint (pf | out, '\n');
                    fprint (pf | out, "((");
                    emit_hityp_ptr (pf | out, hit_sum);
                    fprint (pf | out, "*)");
                    emit_valprim_tmpvar (pf | out, tmp);
                    fprintf (pf | out, ")->atslab_%i = ", @(i));
                    emit_valprim (pf | out, vp);
                    fprint (pf | out, " ;")
                  end
              end // end of [val]
            in
              aux_arg (out, i+1, vps)
            end
          | list_nil () => ()
        end // end of [aux_arg]
      } // end of [where]
    in
      // empty
    end // end of [list_cons]
  | list_nil () => let
      val s2c = d2con_scst_get (d2c)
    in
      case+ 0 of
      | _ when s2cst_is_listlike s2c => begin
          emit_valprim_tmpvar (pf | out, tmp);
          fprint (pf | out, " = (ats_sum_ptr_type)0 ;");
        end
      | _ => begin
          emit_valprim_tmpvar (pf | out, tmp);
          fprint (pf | out, " = (ats_sum_ptr_type)(&");
          emit_d2con (pf | out, d2c);
          fprint (pf | out, ") ;")
        end
    end // end of [list_nil]
end // end of [emit_move_con]

(* ****** ****** *)

(*

// This definition should not be changed!
viewtypedef
arraysize_viewt0ype_int_viewt0ype (a: viewt@ype, n:int) =
  [l:addr | l <> null] (free_gc_v l, @[a][n] @ l | ptr l, int n)

*)

fn emit_instr_arr {m:file_mode} (
    pf: file_mode_lte (m, w)
  | out: &FILE m, tmp: tmpvar_t, asz: int, hit_elt: hityp_t
  ) : void = let
  val () = fprint
    (pf | out, "/* array allocation */\n")
  val () = emit_valprim_tmpvar (pf | out, tmp)
  val () = fprint
    (pf | out, ".atslab_2 = atspre_array_ptr_alloc_tsz (")
  val () = fprint_int (pf | out, asz)
  val () = fprint (pf | out, ", sizeof(")
  val () = emit_hityp (pf | out, hit_elt)
  val () = fprint (pf | out, ")) ;\n")
  val () = emit_valprim_tmpvar (pf | out, tmp)
  val () = fprint (pf | out, ".atslab_3 = ")
  val () = fprint_int (pf | out, asz)
  val () = fprint (pf | out, " ;\n")
in
  // empty
end // end of [emit_instr_arr]

(* ****** ****** *)

fn d2cst_fun_is_void
  (d2c: d2cst_t): bool = begin
  hityp_t_fun_is_void (d2cst_hityp_get_some d2c)
end // end of [funlab_fun_is_void]

fn funlab_fun_is_void
  (fl: funlab_t): bool = begin
  hityp_t_is_void (funlab_typ_res_get fl)
end // end of [funlab_fun_is_void]

fn emit_instr_call {m:file_mode} (
    pf: file_mode_lte (m, w)
  | out: &FILE m
  , tmp: tmpvar_t
  , hit_fun: hityp_t
  , vp_fun: valprim
  , vps_arg: valprimlst
  ) : void = let
  val noret = (
    case+ vp_fun.valprim_node of
    | VPcst d2c => d2cst_fun_is_void (d2c)
    | VPclo (_(*knd*), fl, _(*env*)) => funlab_fun_is_void (fl)
    | VPfun fl => funlab_fun_is_void (fl)
    | _ => hityp_t_fun_is_void hit_fun
  ) : bool
  val () = if noret then fprint (pf | out, "/* ")
  val () = emit_valprim_tmpvar (pf | out, tmp)
  val () = fprint (pf | out, " = ");
  val () = if noret then fprint (pf | out, "*/ ")
  val hit_fun = hityp_decode (hit_fun)
in
  case+ vp_fun.valprim_node of
  | VPcst d2c => let
      val () = emit_d2cst (pf | out, d2c)
      val isfun = $Syn.dcstkind_is_fun (d2cst_kind_get d2c)
      val () = if isfun then () else fprint (pf | out, "$fun")
      val () = fprint (pf | out, " (")
      val () = emit_valprimlst (pf | out, vps_arg)
      val () = fprint (pf | out, ") ;")
    in
      // empty
    end
  | VPclo (knd, fl, envmap) => let
      val entry = funlab_entry_get_some (fl)
      val vtps = funentry_vtps_get_all (entry)
      val () = emit_funlab (pf | out, fl)
      val () = fprint (pf | out, " (")
      val n = emit_cloenv (pf | out, envmap, vtps)
      val () =
        if n > 0 then begin case+ vps_arg of
          | list_cons _ => fprint (pf | out, ", ") | _ => ()
        end
      val () = emit_valprimlst (pf | out, vps_arg)
      val () = fprint (pf | out, ") ;")
    in
      // empty
    end
  | VPfun fl => let
      val () = emit_funlab (pf | out, fl)
      val () = fprint (pf | out, " (")
      val () = emit_valprimlst (pf | out, vps_arg)
      val () = fprint (pf | out, ") ;")
    in
      // empty
    end
  | _ => begin case+ hit_fun.hityp_node of
    | HITfun (fc, hits_arg, hit_res) => begin case+ fc of
      | $Syn.FUNCLOclo _ => let
          val hits_arg = hityplst_encode hits_arg
          val hit_res = hityp_encode hit_res
        in
          fprint (pf | out, "((");
          emit_hityp_clofun (pf | out, hits_arg, hit_res);
          fprint (pf | out, ")(ats_closure_fun(");
          emit_valprim (pf | out, vp_fun);
          fprint (pf | out, "))) (");
          emit_valprim (pf | out, vp_fun);
          if $Lst.list_is_cons (vps_arg) then fprint (pf | out, ", ");
          emit_valprimlst (pf | out, vps_arg);
          fprint (pf | out, ") ;")
        end // end of [$Syn.FUNCLOclo]
      | $Syn.FUNCLOfun _ => let
          val hits_arg = hityplst_encode hits_arg
          val hit_res = hityp_encode hit_res
        in
          fprint (pf | out, "((");
          emit_hityp_fun (pf | out, hits_arg, hit_res);
          fprint (pf | out, ")");
          emit_valprim (pf | out, vp_fun);
          fprint (pf | out, ") (");
          emit_valprimlst (pf | out, vps_arg);
          fprint (pf | out, ") ;")
        end // end of [$Syn.FUNCLOfun]
      end // end of [HITfun]
    | _ => begin
        prerr "Internal Error: emit_instr_call: hit_fun = ";
        prerr hit_fun; prerr_newline ();
        $Err.abort {void} ()
      end
    end
end // end of [emit_instr_call]

(* ****** ****** *)

implement emit_instr {m} (pf | out, ins) = let
  val () = // generating informaion for debugging
    if $Deb.debug_flag_get () > 0 then let
      val () = fprint (pf | out, "/* ")
      val () = fprint_instr (pf | out, ins)
      val () = fprint (pf | out, " */")
      val () = fprint (pf | out, '\n')
    in
      // empty
    end // end of [if]
in
  case+ ins of
  | INSTRarr (tmp, asz, hit_elt) => begin
      emit_instr_arr (pf | out, tmp, asz, hit_elt)
    end
  | INSTRcall (tmp, hit_fun, vp_fun, vps_arg) => begin
      emit_instr_call (pf | out, tmp, hit_fun, vp_fun, vps_arg)
    end
  | INSTRcall_tail fl => begin
      fprint (pf | out, "goto ");
      fprint (pf | out, "__ats_lab_");
      emit_funlab (pf | out, fl);
      fprint (pf | out, " ; // tail call")      
    end
  | INSTRcond (vp_cond, inss_then, inss_else) => begin
      fprint (pf | out, "if (");
      emit_valprim (pf | out, vp_cond);
      fprint (pf | out, ") {\n");
      emit_instrlst (pf | out, inss_then);
      fprint (pf | out, "\n} else {\n");
      emit_instrlst (pf | out, inss_else);
      fprint (pf | out, "\n} /* end of [if] */")
    end
  | INSTRdefine_clo (d2c, fl) => begin
      fprint (pf | out, "ATS_GC_MARKROOT (&");
      emit_d2cst (pf | out, d2c);
      fprint (pf | out, ", sizeof(ats_ptr_type)) ;\n");
      emit_d2cst (pf | out, d2c);
      fprint (pf | out, " = ");
      emit_funlab (pf | out, fl);
      fprint (pf | out, "_closure_make () ;")
    end
  | INSTRdefine_fun (d2c, fl) => begin
      emit_d2cst (pf | out, d2c);
      fprint (pf | out, " = &");
      emit_funlab (pf | out, fl);
      fprint (pf | out, " ;")
    end
  | INSTRdefine_val (d2c, vp) => begin
      fprint (pf | out, "ATS_GC_MARKROOT (&");
      emit_d2cst (pf | out, d2c);
      fprint (pf | out, ", sizeof(");
      emit_hityp (pf | out, vp.valprim_typ);
      fprint (pf | out, ")) ;\n");
      emit_d2cst (pf | out, d2c);
      fprint (pf | out, " = ");
      emit_valprim (pf | out, vp);
      fprint (pf | out, " ;")
    end // end of [INSTRdefine_val]
  | INSTRextval (name, vp) => begin
      fprint (pf | out, "ATS_GC_MARKROOT (&");
      fprint (pf | out, name);
      fprint (pf | out, ", sizeof(");
      emit_hityp (pf | out, vp.valprim_typ);
      fprint (pf | out, ")) ;\n");
      fprint (pf | out, name);
      fprint (pf | out, " = ");
      emit_valprim (pf | out, vp);
      fprint (pf | out, " ;")
    end
  | INSTRfreeptr vp => begin
      fprint (pf | out, "ATS_FREE (");
      emit_valprim (pf | out, vp);
      fprint (pf | out, ") ;")
    end
  | INSTRfunction
      (tmp_ret_all, vps_arg, inss_body, tmp_ret) => let
      val () = funarglst_push (vps_arg)
      val () = emit_instrlst (pf | out, inss_body)
      val () = funarglst_pop ()
      val () = fprint (pf | out, '\n')
    in
      case+ 0 of
      | _ when tmpvar_is_void tmp_ret => begin
          fprint (pf | out, "return /* ");
          emit_valprim_tmpvar (pf | out, tmp_ret);
          fprint (pf | out, " */ ;\n")
        end // end of [_ when ...]
      | _ => begin
          fprint (pf | out, "return ");
          emit_valprim_tmpvar (pf | out, tmp_ret);
          fprint (pf | out, " ;\n")
        end // end of [_]
    end // end of [INSTRfunction]
  | INSTRfunlab fl => begin
      fprint (pf | out, "__ats_lab_");
      emit_funlab (pf | out, fl);
      fprint (pf | out, ':')
    end
  | INSTRdynload_file fil => let
      val () = emit_filename (pf | out, fil)
      val () = fprint (pf | out, "__dynload () ;")
    in
      // empty
    end // end of [INSTRdynload_file]
  | INSTRload_ptr (tmp, vp_ptr) => let
      val () = emit_valprim_tmpvar (pf | out, tmp)
      val () = fprint (pf | out, " = *(")
      val () = emit_hityp (pf | out, tmpvar_typ_get tmp)
      val () = fprint (pf | out, "*)")
      val () = emit_valprim (pf | out, vp_ptr)
      val () = fprint (pf | out, " ;")
    in
      // empty
    end // end of [INSTRload_ptr]
  | INSTRload_ptr_offs (tmp, vp_ptr, offs) => begin
      emit_valprim_tmpvar (pf | out, tmp);
      fprint (pf | out, " = ");
      emit_valprim_select_ptr (pf | out, vp_ptr, offs);
      fprint (pf | out, " ;")
    end // end of [INSTRload_ptr_offs]
  | INSTRload_var_offs (tmp, vp_var, offs) => begin
      emit_valprim_tmpvar (pf | out, tmp);
      fprint (pf | out, " = ");
      emit_valprim_select_var (pf | out, vp_var, offs);
      fprint (pf | out, " ;")
    end // end of [INSTRload_var_offs]
  | INSTRloopexn (_(*knd*), tl) => begin
      fprint (pf | out, "goto ");
      emit_tmplab (pf | out, tl);
      fprint (pf | out, " ;")
    end
  | INSTRmove_arg (arg, vp) => begin
      fprintf (pf | out, "arg%i = ", @(arg));
      emit_valprim (pf | out, vp);
      fprint (pf | out, " ;")
    end
  | INSTRmove_con (tmp, hit_sum, d2c, vps) => begin
      emit_move_con (pf | out, tmp, hit_sum, d2c, vps)
    end
  | INSTRmove_rec_box (tmp, hit_rec, lvps) => let
      fun aux (
          out: &FILE m, tmp: tmpvar_t, lvps: labvalprimlst
        ) :<cloptr1> void = begin case+ lvps of
        | LABVALPRIMLSTcons (l, vp, lvps) => let
            val () = fprint (pf | out, "((")
            val () = emit_hityp_ptr (pf | out, hit_rec)
            val () = fprint (pf | out, "*)")
            val () = emit_valprim_tmpvar (pf | out, tmp)
            val () = fprint (pf | out, ")->atslab_")
            val () = emit_label (pf | out, l)
            val () = fprint (pf | out, " = ")
            val () = emit_valprim (pf | out, vp)
            val () = fprint (pf | out, " ;\n")
          in
            aux (out, tmp, lvps)
          end
        | LABVALPRIMLSTnil () => ()
      end // end of [aux]
    in
      emit_valprim_tmpvar (pf | out, tmp);
      fprint (pf | out, " = ATS_MALLOC (sizeof(");
      emit_hityp_ptr (pf | out, hit_rec);
      fprint (pf | out, ")) ;\n");
      aux (out, tmp, lvps)
    end // end of [INSTRmove_rec_box]
  | INSTRmove_rec_flt (tmp, hit_rec, lvps) => let
      fun aux (
          out: &FILE m, tmp: tmpvar_t, lvps: labvalprimlst
        ) : void = begin case+ lvps of
        | LABVALPRIMLSTcons (l, v, lvps) => let
            val () = emit_valprim_tmpvar (pf | out, tmp)
            val () = fprint (pf | out, ".atslab_")
            val () = emit_label (pf | out, l)
            val () = fprint (pf | out, " = ")
            val () = emit_valprim (pf | out, v)
            val () = fprint (pf | out, " ;\n")
          in
            aux (out, tmp, lvps)
          end
        | LABVALPRIMLSTnil () => ()
      end // end of [aux]
    in
      aux (out, tmp, lvps)
    end // end of [INSTRmove_rec_flt]
  | INSTRmove_ref (tmp, vp) => begin
      fprint (pf | out, "ats_instr_move_ref_mac (");
      emit_valprim_tmpvar (pf | out, tmp);
      fprint (pf | out, ", ");
      emit_hityp (pf | out, vp.valprim_typ);
      fprint (pf | out, ", ");
      emit_valprim (pf | out, vp);
      fprint (pf | out, ") ;")
    end
  | INSTRmove_val (tmp, vp) => begin case+ 0 of
    | _ when valprim_is_void vp => begin
        fprint (pf | out, "/* ");
        emit_valprim_tmpvar (pf | out, tmp);
        fprint (pf | out, " = ");
        emit_valprim (pf | out, vp);
        fprint (pf | out, " */ ;")
      end
    | _ => begin
        emit_valprim_tmpvar (pf | out, tmp);
        fprint (pf | out, " = ");
        emit_valprim (pf | out, vp);
        fprint (pf | out, " ;")
      end
    end // end of [INSTRmove_val]
  | INSTRpatck (vp, patck, fail) => let
      val fail1 = begin case+ fail of
        | KONTmatpnt mpt => matpnt_kont_get mpt | _ => fail
      end
      val () = begin case+ fail1 of
        | KONTnone () => fprint (pf | out, "// ") | _ => ()
      end
    in
      emit_patck (pf | out, vp, patck, fail)
    end // end of [INSTRpatck]
  | INSTRraise vp_exn => begin
      fprint (pf | out, "ats_raise_exn (");
      emit_valprim (pf | out, vp_exn);
      fprint (pf | out, ") ;")
    end
  | INSTRselect (tmp, vp_root, offs) => let
      val is_void = tmpvar_is_void tmp
      val () = if is_void then fprint (pf | out, "/* ")
      val () = emit_valprim_tmpvar (pf | out, tmp)
      val () = fprint (pf | out, " = ")
      val () = emit_valprim_select (pf | out, vp_root, offs)
      val () = if is_void then fprint (pf | out, " */")
      val () = fprint (pf | out, " ;")
    in
      // empty
    end // end of [INSTRselect]
  | INSTRselcon (tmp, vp_sum, hit_sum, ind) => begin
      emit_tmpvar (pf | out, tmp);
      fprint (pf | out, " = ((");
      emit_hityp_ptr (pf | out, hit_sum);
      fprint (pf | out, "*)");
      emit_valprim (pf | out, vp_sum);
      fprintf (pf | out, ")->atslab_%i", @(ind));
      fprint (pf | out, " ;")
    end
  | INSTRselcon_ptr (tmp, vp_sum, hit_sum, ind) => begin
      emit_tmpvar (pf | out, tmp);
      fprint (pf | out, " = &(((");
      emit_hityp_ptr (pf | out, hit_sum);
      fprint (pf | out, "*)");
      emit_valprim (pf | out, vp_sum);
      fprintf (pf | out, ")->atslab_%i)", @(ind));
      fprint (pf | out, " ;")
    end
  | INSTRstore_ptr (vp_ptr, vp_val) => begin
      fprint (pf | out, "*((");
      emit_hityp (pf | out, vp_val.valprim_typ);
      fprint (pf | out, "*)");
      emit_valprim (pf | out, vp_ptr);
      fprint (pf | out, ") = ");
      emit_valprim (pf | out, vp_val);
      fprint (pf | out, " ;");
    end // end of [INSTRstore_ptr]
  | INSTRstore_ptr_offs (vp_ptr, offs, vp_val) => begin
      emit_valprim_select_ptr (pf | out, vp_ptr, offs);
      fprint (pf | out, " = ");
      emit_valprim (pf | out, vp_val);
      fprint (pf | out, " ;")
    end // end of [INSTRstore_ptr_offs]
  | INSTRstore_var (vp_mut, vp_val) => begin
      emit_valprim (pf | out, vp_mut);
      fprint (pf | out, " = ");
      emit_valprim (pf | out, vp_val);
      fprint (pf | out, " ;");
    end // end of [INSTRstore_var]
  | INSTRstore_var_offs (vp_var, offs, vp_val) => begin
      emit_valprim_select_var (pf | out, vp_var, offs);
      fprint (pf | out, " = ");
      emit_valprim (pf | out, vp_val);
      fprint (pf | out, " ;")
    end // end of [INSTRstore_ptr]
  | INSTRswitch branchlst => begin
      fprint (pf | out, "do {\n");
      emit_branchlst (pf | out, branchlst);
      fprint (pf | out, "} while (0) ;")
    end
  | INSTRtmplabint (tl, i) => begin
      emit_tmplabint (pf | out, tl, i); fprint (pf | out, ':')
    end
  | INSTRtrywith (res_try, tmp_exn, brs) => let
      val () = fprint (pf | out, "ATS_TRYWITH_TRY(")
      val () = emit_valprim_tmpvar (pf | out, tmp_exn)
      val () = fprint (pf | out, ")\n")
      val () = emit_instrlst (pf | out, res_try)
      val () = fprint (pf | out, '\n')
      val () = fprint (pf | out, "ATS_TRYWITH_WITH(")
      val () = emit_valprim_tmpvar (pf | out, tmp_exn)
      val () = fprint (pf | out, ")\n")
      val () = fprint (pf | out, "do {\n")
      val () = emit_branchlst (pf | out, brs)
      val () = fprint (pf | out, "} while (0) ;\n")
      val () = fprint (pf | out, "ATS_TRYWITH_END() ;\n")
    in
      // empty
    end // end of [INSTRtrywith]
  | INSTRvardec tmp => begin
      fprint (pf | out, "/* ");
      emit_hityp (pf | out, tmpvar_typ_get tmp);
      fprint (pf | out, ' ');
      emit_tmpvar (pf | out, tmp);
      fprint (pf | out, " ; */")
    end // end of [INSTRvardec]
  | INSTRwhile (tl_brk, tl_cnt, vp_test, inss_test, inss_body) => let
      val () = fprint (pf | out, "ats_while_beg_mac(")
      val () = emit_tmplab (pf | out, tl_cnt)
      val () = fprint (pf | out, ")\n")
      val () = emit_instrlst (pf | out, inss_test)
      val () = fprint (pf | out, '\n')
      val () = fprint (pf | out, "if (!")
      val () = emit_valprim (pf | out, vp_test)
      val () = fprint (pf | out, ") break ;\n")
      val () = emit_instrlst (pf | out, inss_body)
      val () = fprint (pf | out, '\n')
      val () = fprint (pf | out, "ats_while_end_mac(")
      val () = emit_tmplab (pf | out, tl_brk)
      val () = fprint (pf | out, ", ")
      val () = emit_tmplab (pf | out, tl_cnt)
      val () = fprint (pf | out, ")")
    in
      // empty
    end // end of [INSTRwhile]
  | _ => begin
      prerr "Internal Error: emit_instr: ins = "; prerr ins; prerr_newline ();
      $Err.abort {void} ()
    end
end // end of [emit_instr]

implement emit_instrlst {m} (pf | out, inss) = let
  fun aux (out: &FILE m, i: int, inss: instrlst)
    : void = begin case+ inss of
    | list_cons (ins, inss) => begin
        if i > 0 then fprint (pf | out, '\n');
        emit_instr (pf | out, ins); aux (out, i+1, inss)
      end
    | list_nil () => begin
        if i > 0 then () else fprint (pf | out, "/* empty */")
      end
  end // end of [aux]
in
  aux (out, 0, inss)
end // end of [emit_instrlst]    

(* ****** ****** *)

extern fun emit_funarg {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, hits: hityplst_t): void

implement emit_funarg {m} (pf | out, hits) = let
  fun aux (out: &FILE m, i: int, hits: hityplst): void =
    case+ hits of
    | list_cons (hit, hits) => let
        val () = if i > 0 then fprint (pf | out, ", ")
        val () = _emit_hityp (pf | out, hit)
        val () = // variarity needs to be properly handled
          if hityp_is_vararg hit then () else begin
            fprint (pf | out, " arg"); fprint_int (pf | out, i)
          end
      in
        aux (out, i + 1, hits)
      end
    | list_nil () => ()
in
  aux (out, 0, hityplst_decode hits)
end // end of [emit_funarg]

(* ****** ****** *)

extern fun emit_funenvarg {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, vtps: vartypset): int

local

dataviewtype ENV (l:addr, i:addr) = ENVcon (l, i) of (ptr l, ptr i)

fn _emit_funenvarg {m:file_mode} {l:addr} (
    pf_mod: file_mode_lte (m, w)
  , pf_fil: !FILE m @ l
  | p_l: ptr l, vtps: vartypset
  ) : int = let
  var i: int = 0
  viewdef V = (FILE m @ l, int @ i)
  viewtypedef VT = ENV (l, i)
  fn f_arg (pf: !V | vtp: vartyp_t, env: !VT): void = let
    prval @(pf_fil, pf_int) = pf
    val+ ENVcon (p_l, p_i)= env
    val i = !p_i; val () = (!p_i := i + 1)
    val d2v = vartyp_var_get (vtp)
    val hit = (
      if d2var_is_mutable (d2v) then hityp_encode hityp_ptr
      else vartyp_typ_get (vtp)
    ) : hityp_t
    val () = if i > 0 then fprint (pf_mod | !p_l, ", ")
    val () = emit_hityp (pf_mod | !p_l, hit) // type specifier
    val () = fprintf (pf_mod | !p_l, " env%i", @(i)) // arg
  in
    pf := @(pf_fil, pf_int); fold@ env
  end
  val env = ENVcon (p_l, &i)
  prval pf = @(pf_fil, view@ i)
  val () = vartypset_foreach_main {V} {VT} (pf | vtps, f_arg, env)
  prval () = (pf_fil := pf.0; view@ i := pf.1)
  val+ ~ENVcon (_, _) = env
in
  i // the number of environment variables
end // end of [_emit_funenvarg]

in // in of [local]

implement emit_funenvarg (pf | out, vtps) =
  _emit_funenvarg (pf, view@ out | &out, vtps)

end // end of [local]

(* ****** ****** *)

fn funentry_env_err
  (loc: loc_t, fl: funlab_t, vtps: vartypset)
  : void = let
  val d2vs = vartypset_d2varlst_make (vtps)
  val n = $Lst.list_vt_length (d2vs)
  val () =
    if n > 0 then begin
      $Loc.prerr_location loc; prerr ": error(ccomp)"
    end
  val () =
    if n > 1 then begin
      prerr ": the dynamic variables ["
    end else begin
      if n > 0 then begin
        prerr ": the dynamic variable ["
      end
    end // end of [if]
  fun aux (d2vs: d2varlst_vt, i: int): void = begin
    case+ d2vs of
    | ~list_vt_cons (d2v, d2vs) => begin
        if i > 0 then prerr ", "; prerr d2v; aux (d2vs, i+1)
      end
    | ~list_vt_nil () => ()
  end // end of [aux]
  val () = aux (d2vs, 0)
  val () =
    if n > 1 then begin
      prerr "] are not function arguments."
    end else begin
      if n > 0 then begin
        prerr "] is not a function argument."
      end
    end // end of [if]
  val () = begin
    if n > 0 then prerr_newline ()
  end
in
  if n > 0 then $Err.abort {void} ()
end // end of [funentry_env_err]

(* ****** ****** *)

extern fun emit_closure_type {m:file_mode} (
  pf_mod: file_mode_lte (m, w) | out: &FILE m, fl: funlab_t, vtps: vartypset
) : void

extern fun emit_closure_make {m:file_mode} (
  pf_mod: file_mode_lte (m, w) | out: &FILE m, fl: funlab_t, vtps: vartypset
) : void

extern fun emit_closure_clofun {m:file_mode} (
  pf_mod: file_mode_lte (m, w) | out: &FILE m, fl: funlab_t, vtps: vartypset
) : void

local

dataviewtype ENV (l:addr, i:addr) = ENVcon2 (l, i) of (ptr l, ptr i)

fn _emit_closure_type {m:file_mode} {l:addr} (
    pf_mod: file_mode_lte (m, w), pf_fil: !FILE m @ l
  | p_l: ptr l, fl: funlab_t, vtps: vartypset
  ) : void = let
  var i: int = 0
  viewdef V = (FILE m @ l, int @ i)
  viewtypedef VT = ENV (l, i)
  fn f_fld (pf: !V | vtp: vartyp_t, env: !VT): void = let
    prval @(pf_fil, pf_int) = pf
    val+ ENVcon2 (p_l, p_i)= env
    val i = !p_i; val () = (!p_i := i + 1)
    val d2v = vartyp_var_get (vtp)
    val hit = (
      if d2var_is_mutable (d2v) then hityp_encode hityp_ptr
      else vartyp_typ_get (vtp)
    ) : hityp_t
    val () = emit_hityp (pf_mod | !p_l, hit)
    val () = fprintf (pf_mod | !p_l, " closure_env_%i ;\n", @(i))
  in
    pf := @(pf_fil, pf_int); fold@ env
  end

  val () = fprint (pf_mod | !p_l, "typedef struct {\n")
  val () = fprint (pf_mod | !p_l, "ats_fun_ptr_type closure_fun ;\n")

  val env = ENVcon2 (p_l, &i)
  prval pf = @(pf_fil, view@ i)
  val () = vartypset_foreach_main {V} {VT} (pf | vtps, f_fld, env)
  prval () = (pf_fil := pf.0; view@ i := pf.1)
  val+ ~ENVcon2 (_, _) = env

  val () = fprint (pf_mod | !p_l, "} ")
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = fprint (pf_mod | !p_l, "_closure_type ;")
in
  // empty
end // end of [_emit_closure_type]

//

fn _emit_closure_make {m:file_mode} {l:addr} (
    pf_mod: file_mode_lte (m, w), pf_fil: !FILE m @ l
  | p_l: ptr l, fl: funlab_t, vtps: vartypset
  ) : void = let
  var i: int // uninitialized
  viewdef V = (FILE m @ l, int @ i)
  viewtypedef VT = ENV (l, i)
  fn f_arg (pf: !V | vtp: vartyp_t, env: !VT): void = let
    prval @(pf_fil, pf_int) = pf
    val+ ENVcon2 (p_l, p_i) = env
    val i = !p_i; val () = (!p_i := i + 1)
    val d2v = vartyp_var_get (vtp)
    val hit = (
      if d2var_is_mutable (d2v) then hityp_encode hityp_ptr
      else vartyp_typ_get (vtp)
    ) : hityp_t
    val () = if i > 0 then fprint (pf_mod | !p_l, ", ")
    val () = emit_hityp (pf_mod | !p_l, hit)
    val () = fprintf (pf_mod | !p_l, " env%i", @(i))
  in
    pf := @(pf_fil, pf_int); fold@ env
  end

  fn f_body (pf: !V | vtp: vartyp_t, env: !VT): void = let
    prval @(pf_fil, pf_int) = pf
    val+ ENVcon2 (p_l, p_i) = env
    val i = !p_i; val () = (!p_i := i + 1)
    val () = begin
      fprintf (pf_mod | !p_l, "p->closure_env_%i = env%i ;\n", @(i, i))
    end
  in
    pf := @(pf_fil, pf_int); fold@ env
  end

  val () = fprint (pf_mod | !p_l, "ats_clo_ptr_type\n")
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = fprint (pf_mod | !p_l, "_closure_make (")

  val env = ENVcon2 (p_l, &i)

  val () = i := 0
  prval pf = @(pf_fil, view@ i)
  val () = vartypset_foreach_main {V} {VT} (pf | vtps, f_arg, env)
  prval () = (pf_fil := pf.0; view@ i := pf.1)

  val () = fprint (pf_mod | !p_l, ") {\n")
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = begin
    fprint (pf_mod | !p_l, "_closure_type *p = ATS_MALLOC (sizeof (")
  end
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = fprint (pf_mod | !p_l, "_closure_type)) ;\n")
  val () = fprint (pf_mod | !p_l, "p->closure_fun = (ats_fun_ptr_type)&")
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = fprint (pf_mod | !p_l, "_clofun ;\n")

  val () = i := 0
  prval pf = @(pf_fil, view@ i)
  val () = vartypset_foreach_main {V} {VT} (pf | vtps, f_body, env)
  prval () = (pf_fil := pf.0; view@ i := pf.1)

  val+ ~ENVcon2 (_, _) = env

  val () = fprint (pf_mod | !p_l, "return (ats_clo_ptr_type)p ;\n")
  val () = fprint (pf_mod | !p_l, "} /* end of function */")

in
  // empty
end // end of [_emit_closure_make]

dataviewtype ENV (l:addr, i:addr) = ENVcon3 (l, i) of (funlab_t, ptr l, ptr i)

fn _emit_closure_clofun {m:file_mode} {l:addr} (
    pf_mod: file_mode_lte (m, w), pf_fil: !FILE m @ l
  | p_l: ptr l, fl: funlab_t, vtps: vartypset
  ) : void = let
  // function header
  val hit_res = funlab_typ_res_get (fl)
  val () = emit_hityp (pf_mod | !p_l, hit_res)
  val () = fprint (pf_mod | !p_l, '\n')
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = fprint (pf_mod | !p_l, "_clofun (ats_clo_ptr_type cloptr")
  val hits_arg = funlab_typ_arg_get (fl)
  val () = begin case+ 0 of
    | _ when hityplst_is_cons hits_arg => fprint (pf_mod | !p_l, ", ")
    | _ => ()
  end
  val () = emit_funarg (pf_mod | !p_l, hits_arg)
  val () = fprint (pf_mod | !p_l, ") {\n")

  var i: int = 0
  viewdef V = (FILE m @ l, int @ i)
  viewtypedef VT = ENV (l, i)
  fn f_env (pf: !V | vtp: vartyp_t, env: !VT): void = let
    prval @(pf_fil, pf_int) = pf
    val+ ENVcon3 (fl, p_l, p_i) = env
    val i = !p_i; val () = (!p_i := i + 1)
    val () = if i > 0 then fprint (pf_mod | !p_l, ", ")
    val () = fprint (pf_mod | !p_l, "((")
    val () = emit_funlab (pf_mod | !p_l, fl)
    val () = begin
      fprintf (pf_mod | !p_l, "_closure_type*)cloptr)->closure_env_%i", @(i))
    end
  in
    pf := @(pf_fil, pf_int); fold@ env
  end

  // function body
  val is_void = hityp_t_is_void (hit_res)

  val () = begin
    if is_void then () else fprint (pf_mod | !p_l, "return ")
  end

  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = fprint (pf_mod | !p_l, " (")

  val env = ENVcon3 (fl, p_l, &i)
  prval pf = @(pf_fil, view@ i)
  val () = vartypset_foreach_main {V} {VT} (pf | vtps, f_env, env)
  prval () = (pf_fil := pf.0; view@ i := pf.1)
  val+ ~ENVcon3 (_, _, _) = env

  val () = // print a comma for separation if needed
    if i > 0 then begin case+ 0 of
      | _ when hityplst_is_cons hits_arg => fprint (pf_mod | !p_l, ", ")
      | _ => ()
    end

  val hits_arg = hityplst_decode (hits_arg)
  val () = emit_arglst (!p_l, 0, hits_arg) where {
    fun emit_arglst (out: &FILE m, i: int, hits: hityplst)
      : void = begin case+ hits of
      | list_cons (hit, hits) => let
          val () = begin
            if i > 0 then fprint (pf_mod | out, ", ")
          end
          val () = fprintf (pf_mod | out, "arg%i", @(i))
        in
          emit_arglst (out, i+1, hits)
        end // end of [list_cons]
      | list_nil () => ()
    end // end of [emit_arglst]
  } // end of [where]
  val () = fprint (pf_mod | !p_l, ") ;")

  val () = begin
    if is_void then fprint (pf_mod | !p_l, " return ;") else ()
  end

  val () = fprint (pf_mod | !p_l, "\n} /* end of function */")
in
  // empty
end // end of [_emit_clofun]

in // in of [local]

implement emit_closure_type (pf | out, fl, vtps) =
  _emit_closure_type (pf, view@ out | &out, fl, vtps)

implement emit_closure_make (pf | out, fl, vtps) =
  _emit_closure_make (pf, view@ out | &out, fl, vtps)

implement emit_closure_clofun (pf | out, fl, vtps) =
  _emit_closure_clofun (pf, view@ out | &out, fl, vtps)

end // end of [local]

(* ****** ****** *)

implement emit_funentry (pf | out, entry) = let
  val fl = funentry_lab_get (entry)
(*
  val () = begin
    prerr "emit_funentry: fl = "; prerr_funlab fl; prerr_newline ()
  end
*)
  val fc = funlab_funclo_get (fl)
  val hits_arg = funlab_typ_arg_get (fl)
  val hit_res = funlab_typ_res_get (fl)
  val vtps_all = funentry_vtps_get_all (entry)
(*
  val () = begin
    prerr "emit_funentry: vtps_all = "; prerr_vartypset vtps_all;
    prerr_newline ()
  end
*)
  val () = begin case+ fc of
    | $Syn.FUNCLOfun () => begin
        funentry_env_err (funentry_loc_get entry, fl, vtps_all)
      end
    | $Syn.FUNCLOclo _ => ()
  end
(*
  val () = begin
    prerr "emit_funentry: after [funentry_env_err]"; prerr_newline ()
  end
*)
  val tmp_ret = funentry_ret_get (entry)
  val () = funentry_varindmap_set (vtps_all)

  // function head
  val () = begin
     emit_hityp (pf | out, hit_res); fprint (pf | out, '\n')
  end
  val () = begin
    emit_funlab (pf | out, fl); fprint (pf | out, " (")
  end
  val n = emit_funenvarg (pf | out, vtps_all)
  val () = // comma separation if needed
    if n > 0 then begin case+ 0 of
      | _ when hityplst_is_cons hits_arg => fprint (pf | out, ", ")
      | _ => ()
    end
  val () = begin
    emit_funarg (pf | out, hits_arg); fprint (pf | out, ") {\n")
  end

  // local variable declaration
  val () = let
    val () = fprint (pf | out, "/* local vardec */\n")
    val tmps_local = funentry_tmpvarmap_gen (entry)
    val n = emit_tmpvarmap_dec_local (pf | out, tmps_local)
    val () = if n > 0 then fprint (pf | out, '\n')
  in
    tmpvarmap_free (tmps_local)
  end

  // mutual tail-recursion
  val tjs = funentry_tailjoin_get (entry)
  val istailjoin = (case+ tjs of
    | TAILJOINLSTcons _ => true | TAILJOINLSTnil () => false
  ) : bool
  val () = begin
    if istailjoin then emit_tailjoinlst (pf | out, tjs)
  end

  // function body
  val () = emit_instrlst (pf | out, funentry_body_get entry)

  // varindmap needs to be reset
  val () = funentry_varindmap_reset ()

  // return
  val () = fprint (pf | out, "\nreturn ")
  val () = let
    val is_void = tmpvar_is_void (tmp_ret)
    val () = if is_void then fprint (pf | out, "/* ")
    val () = fprint (pf | out, "(")
    val () = emit_tmpvar (pf | out, tmp_ret)
    val () = fprint (pf | out, ")")
    val () = if is_void then fprint (pf | out, " */")
  in
    // empty
  end
  val () = fprint (pf | out, " ;\n} /* end of [")
  val () = begin
    emit_funlab (pf | out, fl); fprint (pf | out, "] */")
  end

  // closure_type and closure_make and clofun
  val () = case+ 0 of
    | _ when istailjoin => ()
    | _ => begin case+ fc of
      | $Syn.FUNCLOclo _ => let
          val () = fprint (pf | out, "\n\n")
          val () = emit_closure_type (pf | out, fl, vtps_all)
          val () = fprint (pf | out, "\n\n")
          val () = emit_closure_make (pf | out, fl, vtps_all)
          val () = fprint (pf | out, "\n\n")
          val () = emit_closure_clofun (pf | out, fl, vtps_all)
        in
          // empty
        end
      | $Syn.FUNCLOfun _ => ()
      end // end of [_]
in
  // empty
end // end of [emit_funentry]

(* ****** ****** *)

implement emit_funentry_prototype {m} (pf | out, entry) = let
  val fl = funentry_lab_get (entry)
  val fc = funlab_funclo_get (fl)
  val hits_arg = funlab_typ_arg_get (fl)
  val hit_res = funlab_typ_res_get (fl)
  val vtps_all = funentry_vtps_get_all (entry)

  fn aux_function
    (out: &FILE m):<cloptr1> void = let
    val () = fprint (pf | out, "static ")
    val () = emit_hityp (pf | out, hit_res)
    val () = fprint (pf | out, ' ')
    val () = emit_funlab (pf | out, fl)
    val () = fprint (pf | out, " (")
    val n = emit_funenvarg (pf | out, vtps_all)
    val () = // comma separation if needed
      if n > 0 then begin case+ 0 of
        | _ when hityplst_is_cons hits_arg => fprint (pf | out, ", ")
        | _ => ()
      end
    val () = emit_funarg (pf | out, hits_arg)
    val () = fprint (pf | out, ") ;\n")
  in
    // empty
  end // end of [aux_function]

  fn aux_closure_make (out: &FILE m):<cloptr1> void = let
    val () = fprint (pf | out, "static ats_clo_ptr_type ")
    val () = emit_funlab (pf | out, fl)
    val () = fprint (pf | out, "_closure_make (")
    val _(*int*) = emit_funenvarg (pf | out, vtps_all)
    val () = fprint (pf | out, ") ;\n")
  in
    // empty
  end // end of [aux_closure_make]

  fn aux_closure_clofun (out: &FILE m):<cloptr1> void = let
    val () = fprint (pf | out, "static ")
    val () = emit_hityp (pf | out, hit_res)
    val () = fprint (pf | out, ' ')
    val () = emit_funlab (pf | out, fl)
    val () = fprint (pf | out, "_clofun (ats_clo_ptr_type cloptr")
    val () = begin case+ 0 of
      | _ when hityplst_is_cons hits_arg => fprint (pf | out, ", ")
      | _ => ()
    end
    val () = emit_funarg (pf | out, hits_arg)
    val () = fprint (pf | out, ") ;\n")
  in
    // empty
  end // end of [aux_closure_clofun]

in
  case+ funlab_qua_get (fl) of
  | D2CSTOPTsome _(*d2c*) => begin case+ fc of
    | $Syn.FUNCLOclo _ => let
        val () = aux_closure_make (out)
        val () = aux_closure_clofun (out)
      in
        // empty
      end
    | $Syn.FUNCLOfun () => ()
    end // end of [D2CSTOPTsome]
  | D2CSTOPTnone () => begin case+ fc of
    | $Syn.FUNCLOclo _ => let
        val () = aux_function (out)
        val () = aux_closure_make (out)
        val () = aux_closure_clofun (out)
      in
        // empty
      end
    | $Syn.FUNCLOfun () => let
        val () = aux_function (out)
      in
        // empty
      end
    end // end of [D2CSTOPTnone]
end // end of [emit_funentry_prototype]

(* ****** ****** *)

implement emit_mainfun (pf | out, fil) = let
  val () = fprint (pf | out, "int main (int argc, char *argv[]) {\n")

  val () = fprint (pf | out, "ATS_GC_INIT() ;\n")

  val () = fprint (pf | out, "mainats_prelude() ;\n")

  val () = fprint (pf | out, "\n#ifndef _ATS_DYNLOADFUN_NONE\n")
  val () = emit_filename (pf | out, fil)
  val () = fprint (pf | out, "__dynload () ;\n")
  val () = fprint (pf | out, "#endif\n\n")

  val () = fprint (pf | out, "mainats ((ats_int_type)argc, (ats_ptr_type)argv) ;\n")

  val () = fprint (pf | out, "return (0) ;\n")

  val () = fprint (pf | out, "} /* end of main */\n")
in
  // empty
end // end of [emit_mainfun]

(* ****** ****** *)

(* end of [ats_ccomp_emit.dats] *)
