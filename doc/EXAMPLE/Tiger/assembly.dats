(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

//
// some extra effort is taken in coding so as to avoid
// generation of garbage as much as possible
//

(* ****** ****** *)

staload TL = "templab.sats"
typedef templst = List ($TL.temp_t)
typedef lablst = List ($TL.label_t)

(* ****** ****** *)

staload "assembly.sats"

(* ****** ****** *)

viewtypedef charlst_vt = List_vt char

extern fun string_make_list_vt_rev (cs: charlst_vt): string

%{^

static inline
ats_ptr_type string_alloc (ats_int_type n) {
  char *p = ATS_ALLOC (n+1) ; p[n] = '\000'; return p;
} // end of [string_alloc]

%}

implement
  string_make_list_vt_rev (cs) = loop (str, cs, n-1) where {
  fun loop {n,i:nat | i <= n} .<i>.
    (str: string n, cs: list_vt (char, i), i1: int (i-1)): string =
    case+ cs of
    | ~list_vt_cons (c, cs) => let
        val c = char1_of_char c; val () = assert (c <> '\000')
      in
        str[i1] := c; loop {n,i-1} (str, cs, i1-1)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => str
  // end of [loop]
  val n = list_vt_length (cs)
  val str = string_alloc (n) where {
    extern fun string_alloc {n:nat} (n: int n): string n = "string_alloc"
  } // end of [str]
} // end of [string_make_list_vt_rev]

(* ****** ****** *)

extern fun revapp_string_list_vt (str: string, cs: charlst_vt): charlst_vt

implement revapp_string_list_vt (str, cs) = loop (str, cs, 0) where {
  val str = string1_of_string (str)
  fun loop {m,n:nat} {i:nat | i <= m} .<m-i>.
    (str: string m, cs: list_vt (char, n), i: size_t i): list_vt (char, m+n-i) =
    if string_is_at_end (str, i) then cs else
      loop (str, list_vt_cons (str[i], cs), i+1)
    // end of [if]
  // end of [loop]
} // end of [revapp_string]

(* ****** ****** *)

implement instr_format (tmpfmt, ins) = let
  fn err (asm: string, res: charlst_vt): string = let
    val () = list_vt_free (res)
  in
    prerr "INTERNAL ERROR";
    prerr ": instr_format: illegal instruction: asm = "; prerr asm;
    prerr_newline ();
    exit {string} (1)
  end // end of [err1]
  
  fn* aux1 {n,i:nat | i <= n} .<n-i>. (
      asm: string n, dst: templst, src: templst, jump: lablst, i: size_t i, res: charlst_vt
    ) : string =
    if string_isnot_at_end (asm, i) then let
      val c = asm[i]
    in
      if c <> '`' then let
        val res = list_vt_cons (c, res) in
        aux1 (asm, dst, src, jump, i+1, res)
      end else begin
        aux2 (asm, dst, src, jump, i+1, res)
      end // end of [if]
    end else begin
      string_make_list_vt_rev (res)
    end // end of [if]
  // end of [aux1]

  and aux2 {n,i:nat | i <= n} .<n-i>. (
      asm: string n, dst: templst, src: templst, jump: lablst, i: size_t i, res: charlst_vt
    ) : string =
    if string_isnot_at_end (asm, i) then let
      val c = asm[i]
    in
      case+ c of
      | 's' => aux3 (asm, dst, src, jump, c, i+1, res)
      | 'd' => aux3 (asm, dst, src, jump, c, i+1, res)
      | 'j' => aux3 (asm, dst, src, jump, c, i+1, res)
      | '`' => let
          val res = list_vt_cons ('`', res) in aux1 (asm, dst, src, jump, i+1, res)
        end // end of [val]
      | _ => err (asm, res) // illegal instruction
    end else begin
      err (asm, res) // illegal instruction
    end // end of [if]

  and aux3 {n,i:nat | i <= n} .<n-i>. (
      asm: string n, dst: templst, src: templst, jump: lablst, c: char, i: size_t i, res: charlst_vt  
    ) : string =
    if string_isnot_at_end (asm, i) then let
      val c1 = asm[i]
    in
      if char_isdigit (c1) then let
        val ind = c1 - '0'; val () = assert (ind >= 0)
      in
        case+ c of
        | 's' => let
            val otmp = list_nth_opt (src, ind)
          in
            case+ otmp of
            | ~Some_vt (tmp) => let
                val name = tmpfmt tmp
                val res = revapp_string_list_vt (name, res)
              in
                aux1 (asm, dst, src, jump, i+1, res)
              end // end of [Some_vt]
            | ~None_vt () => err (asm, res)
          end // end of ['s']
        | 'd' => let
            val otmp = list_nth_opt (dst, ind)
          in
            case+ otmp of
            | ~Some_vt (tmp) => let
                val name = tmpfmt tmp
                val res = revapp_string_list_vt (name, res)
              in
                aux1 (asm, dst, src, jump, i+1, res)
              end // end of [Some_vt]
            | ~None_vt () => err (asm, res)
          end // end of ['d']
        | _ (* 'j' *) => let
            val olab = list_nth_opt (jump, ind)
          in
            case+ olab of
            | ~Some_vt lab => let
                val name = $TL.label_name_get (lab)
                val res = revapp_string_list_vt (name, res)
              in
                aux1 (asm, dst, src, jump, i+1, res)
              end // end of [Some_vt]
            | ~None_vt () => err (asm, res)
          end // end of [_]
      end else begin
        err (asm, res) // illegal instruction
      end // end of [if]
    end else begin
      err (asm, res) // illegal instruction
    end // end of [if]
in
  case+ ins of
  | INSTRoper (asm, dst, src, jump) => let
      val asm = string1_of_string asm 
      val res = list_vt_nil () in aux1 (asm, dst, src, jump, 0, res)
    end // end of [INSTRoper]
  | INSTRlabel (asm, _(*lab*)) => asm
  | INSTRmove (asm, dst, src) => let
      val asm = string1_of_string asm
      val dst = '[dst] and src = '[src] and jump = '[]
      val res = list_vt_nil () in aux1 (asm, dst, src, jump, 0, res)
    end // end of [INSTRmove]
end // end of [instr_format]

(* ****** ****** *)

(* end of [assembly.sats] *)
