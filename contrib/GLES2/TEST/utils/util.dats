//
// Author: Artyom Shakhakov (artyom DOT shalkhakov AT gmail DOT com)
// Time: May, 2011
//
(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no need for dynloading at run-time

(* ****** ****** *)

staload "libc/SATS/stdio.sats"

staload "contrib/GLES2/SATS/gl2.sats"

staload "util.sats"

(* ****** ****** *)
//
// primitive file reading functions
//
fn fr_byte (fl: &FILE r): uint = let
  val res = fgetc_err (file_mode_lte_r_r | fl)
in
  if res >= 0 then uint_of res
  else begin
    exit_errmsg {uint 0} (1, "ATS: [image_input]: unexpected end of file\n")
  end // end of [if]
end // end of [fr_byte]

fn fr_short (fl: &FILE r): uint = let
  val r1 = fr_byte fl
  val r2 = fr_byte fl
  val res = r1 lor (r2 << 8)
in
  res
end

fn fr_int (fl: &FILE r): uint = let
  val r1 = fr_short fl
  val r2 = fr_short fl
in
  // bytes are read in this order: X Y Z W
  // and the result is: X lor (Y << 8) lor (Z << 16) lor (W << 24)
  r1 lor (r2 << 16)
end // end of [fr_int]

(* ****** ****** *)

implement shader_from_source (x, src) = let
  val () = glShaderSource__string (x, src)
  val () = glCompileShader x
  var stat: GLint // uninitialized
  val () = glGetShaderiv (x, GL_COMPILE_STATUS, stat)
in
  if int_of_GLint stat = 0 then let
    #define BUFSZ 1024
    var !p_log with pf_log = @[byte][BUFSZ]()
    var len: GLsizei // uninitialized
    prval pf_len = Some_v (view@ (len))
    val () = glGetShaderInfoLog (pf_log, pf_len | x, (GLsizei)BUFSZ, &len, p_log)
    prval Some_v pf = pf_len; prval () = view@ (len) := pf
    val () = print ("Shader compilation error:\n")
    val () = fprint_strbuf (stdout_ref, !p_log) // FIXME: [print_strbuf] doesn't compile
    val () = print_newline ()
    prval () = pf_log := bytes_v_of_strbuf_v (pf_log)
  in
    exit {void} (1)
  end // end of [if]
end // end of [shader_from_source]

(* ****** ****** *)

implement shader_from_file (x, name) = let
  fun file_length {m:fm} (pf_mod: file_mode_lte (m, r) | f: &FILE m): lint = let
    val ofs = ftell_exn f
    val () = fseek_exn (f, lint_of_int 0, SEEK_END)
    val sz = ftell_exn f
    val () = fseek_exn (f, ofs, SEEK_SET)
  in
    sz
  end // end of [file_length]

  extern
  fun fread_b0yte_exn
    {n_buf:int}
    {n:nat | n <= n_buf}
    {m:fm} (
    pf_mod: file_mode_lte (m, r)
  | buf: &b0ytes (n_buf) >> bytes (n_buf), n: size_t n, f: &FILE m
  ) :<!exn> void = "atslib_fread_byte_exn"
  // end of [fread_b0yte_exn]

  val (pfopt | p_ifp) = fopen_err (name, file_mode_r)
in
  if p_ifp > null then let
    prval Some_v (pf) = pfopt
    val len = size1_of_size (size_of_lint (file_length (file_mode_lte_r_r | !p_ifp)))
    val (pfopt_mem | p_mem) = malloc_ngc (len + 1)
  in
    if p_mem > null then let
      prval malloc_v_succ (pf_ngc, pf_mem) = pfopt_mem
      val () = fread_b0yte_exn (file_mode_lte_r_r | !p_mem, len, !p_ifp)
      val () = bytes_strbuf_trans (pf_mem | p_mem, len)
      val (fpf | str) = strbuf_takeout_ptr (pf_mem | p_mem)
      val () = shader_from_source (x, str)
      prval () = fpf (str)
      prval () = pf_mem := bytes_v_of_strbuf_v (pf_mem)
    in
      free_ngc (pf_ngc, pf_mem | p_mem);
      fclose_exn (pf | p_ifp)
    end else let
      prval malloc_v_fail () = pfopt_mem
      val () = prerrf ("[shader_from_file]: failed to allocate %d bytes\n", @(int_of_size len))
    in
      fclose_exn (pf | p_ifp);
      exit {void} (1)
    end // end of [if]
  end else let
    prval None_v () = pfopt
  in
    prerrf ("[shader_from_file]: can't open [%s]\n", @("name"));
    exit {void} (1)
  end // end of [if]
end // end of [shader_from_file]

(* ****** ****** *)
// TGA image loading

fun{a:viewt@ype} matrix_ptr_initialize_fp .< >.
  {v:view} {vt:viewtype} {m,n:nat} {l:addr} (
  pf_v: !v
, pf_mat: !matrix_v (a?, m, n, l) >> matrix_v (a, m, n, l)
| base: ptr l
, col: size_t m, row: size_t n
, f: (!v | size_t, &a? >> a, !vt) -<fun1> void
, env: !vt
) : void = let
  prval (pf1_mul, pf_arr) = array_v_of_matrix_v (pf_mat)
  prval pf_arr = array_v_group (pf1_mul, pf_arr)
  val (pf2_mul | rsz) = row szmul2 sizeof<a>
  var !p_clo with pf_clo = @lam (pf: !v | i: sizeLt m, x: &(@[a?][n]) >> @[a][n], env: !vt): void =<clo1>
    array_ptr_initialize_funenv_tsz {a} {v} {vt} {n} (pf | x, row, f, sizeof<a>, env)
  // end of [p_clo]
  prval () = lemma_arrsz (pf2_mul) where {
    extern prfun lemma_arrsz {p:int} (pf_mul: MUL (n, sizeof a, p))
      :<> [p == sizeof (@[a][n])] void
  } // end of [where]
  val () = array_ptr_initialize_cloenv_tsz {@[a][n]} (pf_v | !base, col, !p_clo, rsz, env)
  prval pf_arr = array_v_ungroup (pf1_mul, pf_arr)
  prval () = pf_mat := matrix_v_of_array_v (pf1_mul, pf_arr)
in
  // nothing
end // end of [matrix_ptr_initialize_fp]

extern
fun image_input (
    fl: &FILE r
  , w: &size_t? >> size_t w
  , h: &size_t? >> size_t h
  , psz: &size_t? >> size_t
  , p: &ptr? >> ptr l
  ) : #[w,h:nat] #[l:addr] (
    matrix_v (uint, w, h, l)
  | (matrix_v (uint, w, h, l) | ptr l) -<lin> void
  )

implement image_input (fl, w, h, psz, p) = let
  val id_len = fr_byte fl
  val () = () where {
    val cmt = fr_byte fl // color map type
    val () = assert_errmsg (cmt = 0u, "[image_input]: color-mapped TGA images not supported\n")
  }
  val imt = fr_byte fl // image type (2 for uncompressed RGB, 3 for uncompressed grayscale
  val () = assert_errmsg (imt = 2u || imt = 3u, "[image_input]: only type 2 (RGB) and 3 (gray) TGA images are supported\n")
  val _ = fr_short fl  // color map index
  val _ = fr_short fl  // color map length
  val _ = fr_byte fl   // color map size
  val ox = fr_short fl // x origin
  val oy = fr_short fl // y origin
  val [m:int] col = uint1_of_uint (fr_short fl) // width
  val col = size1_of_uint1 col
  val [n:int] row = uint1_of_uint (fr_short fl) // height
  val row = size1_of_uint1 row
  val ps = fr_byte fl  // pixel size
  val () = assert_errmsg (imt <> 2u || ps = 32u || ps = 24u, "[image_input]: only 32 or 24 bit images supported (no colormaps\n")
  val () = psz := size_of_uint ps
  val ar = fr_byte fl  // attributes
  // TODO: to support top-down images, may implement
  // [rarray_ptr_initialize_cloenv_tsz]
  val () = assert_errmsg ((ar land 0x20u) = 0u, "[image_input]: only bottom-up TGA images are supported\n")
  val () = fseek_exn (fl, lint_of (int_of_uint id_len), SEEK_CUR) // skip comment
  val (pf1_mul | sz1) = col szmul2 row
  val (pf2_mul | sz2) = sz1 szmul2 sizeof<uint>
  val [l:addr] (pf_optmem | p_mem) = malloc_ngc (sz2)
in
  if p_mem > null then let
    prval malloc_v_succ (pf_ngc, pf_mem) = pf_optmem
    stavar l1: addr
    val p_fl = &fl : ptr l1
    prval pf_arr = array_v_of_bytes_v {uint} (pf2_mul, pf_mem)
    prval pf_mat = matrix_v_of_array_v (pf1_mul, pf_arr)
    // color reading and conversion functions
    typedef finit_type = (!FILE r @ l1 | size_t, &uint? >> uint, !ptr l1) -<fun1> void
    extern val fr8: finit_type
    implement fr8 (pf | i, x, fl) = let
      val b = fr_byte (!fl)
    in
      x := ((255u << 24) lor (b << 16) lor (b << 8) lor b)
    end // end of [fr8]
    extern val fr24: finit_type
    implement fr24 (pf | i, x, f) = let
      val b = fr_byte (!f); val g = fr_byte (!f); val r = fr_byte (!f)
    in
      x := ((255u << 24) lor (b << 16) lor (g << 8) lor r)
    end // end of [fr24]
    extern val fr32: finit_type
    implement fr32 (pf | i, x, f) = let
      val b = fr_byte (!f); val g = fr_byte (!f); val r = fr_byte (!f)
      val a = fr_byte (!f)
    in
      x := ((a << 24) lor (b << 16) lor (g << 8) lor r)
    end // end of [fr32]
    val appf = begin
      case+ 0 of
      | _ when ps = 8u => fr8
      | _ when ps = 24u => fr24
      | _ when ps = 32u => fr32
      | _ => exit_errmsg (1, "[image_input]: illegal pixel size\n")
    end // end of [begin]
    val () = matrix_ptr_initialize_fp<uint> {FILE r @ l1} {ptr l1} {m,n} {l} (
      view@ (fl), pf_mat
    | p_mem, col, row, appf, p_fl
    ) // end of [val]
  in
    w := col; h := row; p := p_mem;
    #[.. | (pf_mat | lam (pf_mat | p_mat) =<lin> let
      prval (pf_mul, pf_arr) = array_v_of_matrix_v (pf_mat)
      prval () = mul_isfun (pf_mul, pf1_mul)
      prval (pf_mul, pf_mem) = bytes_v_of_array_v {uint} (pf_arr)
      prval () = mul_isfun (pf_mul, pf2_mul)
    in
      free_ngc (pf_ngc, pf_mem | p_mat)
    end) ]
  end else let
    prval malloc_v_fail () = pf_optmem
    #define s2i int1_of_size1
  in
    prerrf ("[image_input]: failed to allocate %d bytes (for %dx%d image)\n", @(s2i sz2, s2i col, s2i row));
    // by insistence of typechecker ...
    w := size1_of_int1 0; h := size1_of_int1 0; p := null;
    exit (1)
  end // end of [if]
end // end of [image_input]

implement texture_from_file (tex, filename): void = let
  val (pf_fl | p_fl) = fopen_exn (filename, file_mode_r)
  var imw: size_t and imh: size_t and psz: size_t and p_im: ptr // uninitialized
  val (pf_mat | free) = image_input (!p_fl, imw, imh, psz, p_im)
  val () = fclose_exn (pf_fl | p_fl)
in
  glBindTexture (GL_TEXTURE_2D, tex);
  TexImage2D (
      GL_TEXTURE_2D, (GLint)0, ifmt
    , (GLsizei)imw, (GLsizei)imh
    , 0, GL_RGBA, GL_UNSIGNED_BYTE, !p_im
    ) where {
    val ifmt = if psz = 24 then GL_RGB else GL_RGBA
    extern
    fun TexImage2D
      {a:t@ype} {w,h:int} (
      target: GLenum
    , level: GLint
    , internalFormat: GLenum
    , width: GLsizei w
    , height: GLsizei h
    , border: natLt(2)
    , format: GLenum
    , type: GLenum_type (a)
    , texels: &mtrxt (uint, w, h)
    ) : void
      = "mac#atsctrb_glTexImage2D"
    // end of [TexImage2D]
  }; // end of [where]
  glTexParameteri (GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri (GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  glTexParameteri (GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
  glTexParameteri (GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
  free (pf_mat | p_im)
end // end of [texture_from_file]
