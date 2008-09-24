(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
 * Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

// July 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "top.sats"

(* ****** ****** *)

extern fun errmsg {a:viewt@ype} (msg: string): a
implement errmsg (msg) = (prerr msg; prerr_newline (); exit 1)

//

#define BASE 8
#define c2i int_of_char
#define i2c char_of_int

//


extern fun char_get (): char = "char_get"
extern fun char_update (): void = "char_update"
extern fun char_get_update (): char = "char_get_update"
extern fun char_update_get (): char = "char_update_get"

extern fun pos_prev_reset (): void = "pos_prev_reset"

%{^

static int the_line_cnt = 1 ;
static int the_line_cnt_prev = 1 ;
static int the_char_cnt = 0 ;
static int the_char_cnt_prev = 0 ;

//static inline
ats_int_type pos_line_get () { return the_line_cnt ; }

//static inline
ats_int_type pos_char_get () { return the_char_cnt ; }

//static inline
ats_int_type pos_line_prev_get () { return the_line_cnt_prev ; }

//static inline
ats_int_type pos_char_prev_get () { return the_char_cnt_prev ; }

static inline
ats_void_type pos_prev_reset () {
  the_line_cnt_prev = the_line_cnt ;
  the_char_cnt_prev = the_char_cnt ;
  return ;  
}

//

static inline
ats_void_type
pos_advance (ats_char_type c) {
  switch (c) {
    case '\n':
      ++the_line_cnt ; the_char_cnt = 0 ; break ;
    default: ++the_char_cnt ; break ;
  }
  return ;
}

static ats_char_type the_char ;

static inline
ats_char_type char_get() { return the_char ; }

static inline
ats_void_type char_update() { 
  the_char = getchar () ;
  pos_advance (the_char) ;
  return ;
}

static inline
ats_char_type char_get_update() {
  char c = the_char ;
  the_char = getchar () ;
  pos_advance (the_char) ;
  return c ;
}

static inline
ats_char_type char_update_get() {
  the_char = getchar () ;
  pos_advance (the_char) ;
  return the_char ;
}

%}

(* ****** ****** *)

// implemented in [position.dats]
extern fun position_get (): pos_t = "position_get"
extern fun position_prev_get (): pos_t = "position_prev_get"

(* ****** ****** *)

dataviewtype chars (int) =
  | chars_nil (0)
  | {n:nat} chars_cons (n+1) of (char, chars n)

#define nil chars_nil
#define :: chars_cons

extern fun chars_reverse {n:nat} (cs: chars n):<> chars n
implement chars_reverse (cs) = let
  fun loop {i,j:nat} .<i>.
    (cs1: chars i, cs2: chars j):<> chars (i+j) =
    case+ cs1 of
    | c :: !cs1_r => let
        val cs1_v = !cs1_r
      in
        !cs1_r := cs2; fold@ (cs1); loop (cs1_v, cs1)
      end
    | ~nil() => cs2
in
  loop (cs, nil ())
end // chars_reverse
     
//

extern fun chars_is_nil {n:nat} (cs: !chars n): bool (n == 0) =
  "chars_is_nil"

implement chars_is_nil (cs) = case+ cs of
  | nil () => (fold@ cs; true) | _ :: _ => (fold@ cs; false)

extern fun
chars_uncons {n:pos} (cs: &chars n >> chars (n-1)): char =
  "chars_uncons"

implement chars_uncons (cs) =
  let val ~(c :: cs1) = cs in cs := cs1; c end

fun chars_free {n:nat} (cs: chars n): void =
  case+ cs of ~(c :: cs) => chars_free cs | ~nil () => ()

//

extern fun
string_make_chars_int {n:nat} (cs: chars n, n: int n): string n =
  "string_make_chars_int"

%{

ats_ptr_type
string_make_chars_int (ats_ptr_type cs, const ats_int_type n) {
  char *s0, *s;

  s0 = ats_malloc_gc(n+1) ;
  s = s0 + n ;
  *s = '\0' ; --s ;

  while (!chars_is_nil(cs)) { *s = chars_uncons(&cs) ; --s ; }

  return s0 ;
}

%}

(* ****** ****** *)

implement tokenize_line_comment () = let

fun loop (): void =
  let
    val c = char_get ()
  in
    if c >= '\0' then
      (char_update (); if c <> '\n' then loop () else ())
    else ()
  end

in

  loop ()

end // end of [tokenize_line_comment]

(* ****** ****** *)

implement tokenize_rest_text () = let

fun loop {n:nat} (cs: chars n, n: int n): string =
  let
    val c = char_get ()
  in
    if c >= '\0' then begin
      char_update (); loop (c :: cs, n+1)
    end else begin
      string_make_chars_int (cs, n)
    end
  end

in

  loop (nil (), 0)

end // end of [tokenize_rest_text]

(* ****** ****** *)

fun errmsg_unclosed_logue {a:viewt@ype} (): a =
  let
    val pos = position_prev_get ()
  in
    prerr_string ("The logue starting at [");
    prerr_pos pos;
    prerr_string ("] is not closed.");
    prerr_newline ();
    exit {a} (1)
  end

implement tokenize_logue () = let

fun loop {n,l:nat} (cs: chars n, n: int n, l: int l): string = let
  val c = char_get ()
in
  if c >= '\0' then begin case+ c of
    | '%' => let
        val c1 = char_update_get ()
      in
        case+ c1 of
        | '}' =>
            if l > 0 then begin
              char_update (); loop (c1 :: c :: cs, n+2, l-1)
            end else begin
              char_update (); string_make_chars_int (cs, n)
            end
        | '\{' => (char_update (); loop (c1 :: c :: cs, n+2, l+1))
        | _ => loop (c :: cs, n+1, l)
      end
    | _ => (char_update (); loop (c :: cs, n+1, l))
  end else begin // c = EOF
    chars_free cs; errmsg_unclosed_logue {string} ()
  end
end // end of [loop]

in

loop (nil (), 0, 0)

end // end of [tokenize_logue]

(* ****** ****** *)

fun errmsg_unclosed_funarg {a:viewt@ype} (): a =
  let
    val pos = position_prev_get ()
  in
    prerr_string ("The function argument starting at [");
    prerr_pos pos;
    prerr_string ("] is not closed.");
    prerr_newline ();
    exit {a} (1)
  end

implement tokenize_funarg () = let
  fun loop {n:nat} (cs: chars n, n: int n): string =
    let
       val c = char_get ()
    in
       if c >= '\0' then begin case+ c of
         | ')' =>
           (char_update (); string_make_chars_int (cs, n))
         | _ =>
           (char_update (); loop (c :: cs, n+1))
       end else begin
         chars_free cs; errmsg_unclosed_funarg {string} ()
       end
    end
in
  loop (nil (), 0)
end

(* ****** ****** *)

fun errmsg_char_esc (): char =
  let
    val pos = position_prev_get ()
  in
    prerr_string ("The escaped char at [");
    prerr_pos pos;
    prerr_string ("] is not supported.");
    prerr_newline ();
    exit {char} (1)
  end

fun tokenize_char_esc_code (ci: int, i: int): char =
  if i < 2 then
    let
       val c = char_get ()
    in
       if char_isdigit c then
         (char_update (); tokenize_char_esc_code (BASE * ci + (c - '0'), i+1))
       else i2c ci
    end
  else i2c ci

fun tokenize_char_esc () =
  let
     val c = char_get_update ()
  in
     if char_isdigit c then
       tokenize_char_esc_code (c - '0', 0)
     else begin case+ c of
       | 'a' => '\007' (* alert *)
       | 'b' => '\010' (* backspace *)
       | 'f' => '\014' (* line feed *)
       | 'n' => '\012' (* newline *)
       | 'r' => '\015' (* carriage return *)
       | 't' => '\011' (* horizonal tab *)
       | 'v' => '\013' (* vertical tab *)
       | _ => c (* no effect on other chars *)
     end
  end

fun errmsg_unclosed_char {a:viewt@ype} (): a =
  let
    val pos = position_prev_get ()
  in
    prerr_string ("The char starting at [");
    prerr_pos pos;
    prerr_string ("] is not closed.");
    prerr_newline ();
    exit {a} (1)
  end

fun tokenize_char (): char =
  let
     val c0 = char_get ()
     val c = case+ c0 of
       | '\\' => (char_update (); tokenize_char_esc ())
       | '\'' => '\0' (* '' stands for '\0' *)
       | _ => (char_update (); c0)
     val c1 = char_get_update ()
  in
     if c1 <> '\'' then
       errmsg_unclosed_char {char} ()
     else c
  end

(* ****** ****** *)

fun errmsg_unclosed_code {a:viewt@ype} (): a =
  let
    val pos = position_prev_get ()
  in
    prerr_string ("The code starting at [");
    prerr_pos pos;
    prerr_string ("] is not closed.");
    prerr_newline ();
    exit {a} (1)
  end

fun tokenize_code {n,l:nat}
  (cs: chars n, n: int n, l: int l): string =
  let
     val c = char_get ()
  in
     if c >= '\0' then begin case+ c of
       | '\{' =>
         (char_update (); tokenize_code (c :: cs, n+1, l+1))
       | '}' when l > 0 =>
         (char_update (); tokenize_code (c :: cs, n+1, l-1))
       | '}' =>
         (char_update (); string_make_chars_int (cs, n))
       | _ =>
         (char_update (); tokenize_code (c :: cs, n+1, l))
     end else begin
       chars_free cs; errmsg_unclosed_code {string} ()
     end
  end

(* ****** ****** *)

fun errmsg_unclosed_comment {a:viewt@ype} (): a =
  let
    val pos = position_prev_get ()
  in
    prerr_string ("The comment starting at [");
    prerr_pos pos;
    prerr_string ("] is not closed.");
    prerr_newline ();
    exit {a} (1)
  end

fun tokenize_comment {l:nat} (l: int l): void =
  let
     val c = char_get ()
  in
     if c >= '\0' then begin case+ c of
       | '\(' => begin
           case+ char_update_get () of
             | '*' => tokenize_comment (l+1)
             | _ => tokenize_comment l
         end
       | '*' => begin
           case+ char_update_get () of
             | ')' =>
               if l > 0 then tokenize_comment (l-1) else char_update ()
             | _ => tokenize_comment l
         end
       | _ => (char_update (); tokenize_comment l)
     end else begin
       errmsg_unclosed_comment {void} ()
     end
  end

(* ****** ****** *)

fun tokenize_int (i: int): int =
  let val c = char_get () in
    if char_isdigit c then
      (char_update (); tokenize_int (BASE * i + (c - '0')))
    else i
  end 

(* ****** ****** *)

fun tokenize_string_char () =
  let val c = char_get_update () in
    if c = '\\' then tokenize_char_esc () else c
  end

fun errmsg_unclosed_string {a:viewt@ype} (): a =
  let
    val pos = position_prev_get ()
  in
    prerr_string ("The string starting at [");
    prerr_pos pos;
    prerr_string ("] is not closed.");
    prerr_newline ();
    exit {a} (1)
  end

fun tokenize_string {n:nat} (cs: chars n, n: int n): string =
  let
     val c0 = char_get ()
  in
     if c0 >= '\0' then begin
       if c0 = '"' then
         (char_update (); string_make_chars_int (cs, n))
       else let
         val c = tokenize_string_char ()
       in
         tokenize_string (c :: cs, n+1)
       end
     end else begin
       chars_free cs; errmsg_unclosed_string {string} ()
     end
  end

(* ****** ****** *)

fun char_iseof (c: char) = (c < '\0')
fun char_issymbl (c: char): bool =
  string_contains ("!%&#+-/:<=>@\\~`|*", c)

fun tokenize_word_sym {n:nat} (cs: chars n, n: int n): string =
  let
     val c = char_get ()
  in
     if char_issymbl c then
       (char_update (); tokenize_word_sym (c :: cs, n+1))
     else string_make_chars_int (cs, n)
  end

fun tokenize_word_ide {n:nat} (cs: chars n, n: int n): string =
  let
     val c = char_get ()
  in
     if char_isalnum c then
       (char_update (); tokenize_word_ide (c :: cs, n+1))
     else if (c = '_') then
       (char_update (); tokenize_word_ide (c :: cs, n+1))
     else string_make_chars_int (cs, n)
  end

(* ****** ****** *)

extern fun
fprint_token {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | fil: &FILE m, tok: token): void =
  "fprint_token"

implement fprint_token (pf_mod | fil, tok): void = begin
  case+ tok of
  | TOKchar c => fprintf (pf_mod | fil, "char(%c)", @(c))
  | TOKcode s => fprintf (pf_mod | fil, "code(%s)", @(s))
  | TOKint i => fprintf (pf_mod | fil, "int(%i)", @(i))
  | TOKstring s => fprintf (pf_mod | fil, "string(%s)", @(s))
  | TOKword s => fprintf (pf_mod | fil, "word(%s)", @(s))
  | TOKlit c => fprintf (pf_mod | fil, "lit(%c)", @(c))
  | TOKmark s => fprintf (pf_mod | fil, "mark(%s)", @(s))
  | TOKeof () => fprint_string (pf_mod | fil, "EOF")
end // end of [fprint_token]

implement print_token (tok) = let
  val (pf_stdout | ptr_stdout) = stdout_get ()
in
  fprint_token (file_mode_lte_w_w | !ptr_stdout, tok);
  stdout_view_set (pf_stdout | (*none*))
end // end of [print_token]

implement prerr_token (tok) = let
  val (pf_stderr | ptr_stderr) = stderr_get ()
in
  fprint_token (file_mode_lte_w_w | !ptr_stderr, tok);
  stderr_view_set (pf_stderr | (*none*))
end // end of [prerr_token]

(* ****** ****** *)

fun pos_prev_reset_and_char_update (): void =
  (pos_prev_reset (); char_update ())

extern fun tokenize (): token = "tokenize"

implement tokenize () = begin
  let val c = char_get () in case+ c of
    | '\'' => let
        val () = pos_prev_reset_and_char_update ()
      in
        TOKchar (tokenize_char ())
      end // end of ['\'']
    | '\(' => let
        val () = pos_prev_reset_and_char_update ()
      in
        case+ char_get () of
          | '*' => (tokenize_comment (0); tokenize ())
          | _ => TOKlit '\('
      end // end of ['\(']
    | '/' => let
        val () = pos_prev_reset_and_char_update ()
      in
        case+ char_get () of
          | '/' => (tokenize_line_comment (); tokenize ())
          | _ => TOKword (tokenize_word_sym ('/' :: nil (), 1))
      end // end of ['/']
    | '\{' => let
        val () = pos_prev_reset_and_char_update ()
      in
        TOKcode (tokenize_code (nil (), 0, 0))
      end // end of ['\{']
    | '"' => let
        val () = pos_prev_reset_and_char_update ()
      in
        TOKstring (tokenize_string (nil (), 0))
      end // end of ['"']
    | '_' => let
        val () = pos_prev_reset_and_char_update ()
      in
        TOKword (tokenize_word_ide (c :: nil (), 1))
      end // end of ['_']
    | '%' => let
        val () = pos_prev_reset_and_char_update ()
      in
        case+ char_get () of
          | '\{' => (char_update (); TOKmark "%{")
          | _ => TOKword (tokenize_word_sym (c :: nil (), 1))
      end // end of ['%']
    | _ when char_isdigit c => let
        val () = pos_prev_reset_and_char_update ()
      in
        TOKint (tokenize_int (c - '0'))
      end // end of [digit]
    | _ when char_isalpha c => let
        val () = pos_prev_reset_and_char_update ()
      in
        TOKword (tokenize_word_ide (c :: nil (), 1))
      end // end of [alpha]
    | _ when char_issymbl c => let
        val () = pos_prev_reset_and_char_update ()
      in
        TOKword (tokenize_word_sym (c :: nil (), 1))
      end // end of [symbl]
    | _ when char_isspace c => begin
        let val () = char_update () in tokenize () end
      end // end of [space]
    | _ when char_iseof c => let
        val () = pos_prev_reset_and_char_update ()
      in
        TOKeof ()
      end // end of [eof]
    | _ => let
        val () = pos_prev_reset_and_char_update ()
      in
        TOKlit c
      end
  end // end of [let]
end // end of [tokenize]

//

%{

static ats_ptr_type the_token ;

ats_ptr_type token_get () { return the_token ; }

ats_void_type token_update () {
  the_token = tokenize () ;
  return ;
}

ats_ptr_type token_get_update () {
  ats_ptr_type tok = the_token ;
  the_token = tokenize () ;
  return tok;
}

%}

// initialization
val () = (char_update (); token_update ())

(* ****** ****** *)

(* end of [token.dats] *)
