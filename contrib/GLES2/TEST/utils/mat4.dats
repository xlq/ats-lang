//
// Author: Artyom Shakhakov (artyom DOT shalkhakov AT gmail DOT com)
// Time: June, 2011
//
(* ****** ****** *)

staload "libc/SATS/math.sats"

staload "contrib/GLES2/SATS/gl2.sats"

staload "mat4.sats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no need for dynloading at run-time

(* ****** ***** *)

implement mat_mult (m, n) = let
  fun go .< >. (b: &GLmat4, a: &GLmat4):<> void = let
    #define F float_of
    #define G GLfloat_of_float
    var !p = @[GLfloat][16](G 0.0f)
    val ai0 = F a.[0] and ai1 = F a.[1] and ai2 = F a.[2] and ai3 = F a.[3]
    val () = !p.[0] := G (ai0 * F b.[0] + ai1 * F b.[4] + ai2 * F b.[8] + ai3 * F b.[12]);
    val () = !p.[1] := G (ai0 * F b.[1] + ai1 * F b.[5] + ai2 * F b.[9] + ai3 * F b.[13]);
    val () = !p.[2] := G (ai0 * F b.[2] + ai1 * F b.[6] + ai2 * F b.[10] + ai3 * F b.[14]);
    val () = !p.[3] := G (ai0 * F b.[3] + ai1 * F b.[7] + ai2 * F b.[11] + ai3 * F b.[15])

    val ai0 = F a.[4] and ai1 = F a.[5] and ai2 = F a.[6] and ai3 = F a.[7]
    val () = !p.[4] := G (ai0 * F b.[0] + ai1 * F b.[4] + ai2 * F b.[8] + ai3 * F b.[12]);
    val () = !p.[5] := G (ai0 * F b.[1] + ai1 * F b.[5] + ai2 * F b.[9] + ai3 * F b.[13]);
    val () = !p.[6] := G (ai0 * F b.[2] + ai1 * F b.[6] + ai2 * F b.[10] + ai3 * F b.[14]);
    val () = !p.[7] := G (ai0 * F b.[3] + ai1 * F b.[7] + ai2 * F b.[11] + ai3 * F b.[15])  

    val ai0 = F a.[8] and ai1 = F a.[9] and ai2 = F a.[10] and ai3 = F a.[11]
    val () = !p.[8] := G (ai0 * F b.[0] + ai1 * F b.[4] + ai2 * F b.[8] + ai3 * F b.[12]);
    val () = !p.[9] := G (ai0 * F b.[1] + ai1 * F b.[5] + ai2 * F b.[9] + ai3 * F b.[13]);
    val () = !p.[10] := G (ai0 * F b.[2] + ai1 * F b.[6] + ai2 * F b.[10] + ai3 * F b.[14]);
    val () = !p.[11] := G (ai0 * F b.[3] + ai1 * F b.[7] + ai2 * F b.[11] + ai3 * F b.[15])

    val ai0 = F a.[12] and ai1 = F a.[13] and ai2 = F a.[14] and ai3 = F a.[15]
    val () = !p.[12] := G (ai0 * F b.[0] + ai1 * F b.[4] + ai2 * F b.[8] + ai3 * F b.[12]);
    val () = !p.[13] := G (ai0 * F b.[1] + ai1 * F b.[5] + ai2 * F b.[9] + ai3 * F b.[13]);
    val () = !p.[14] := G (ai0 * F b.[2] + ai1 * F b.[6] + ai2 * F b.[10] + ai3 * F b.[14]);
    val () = !p.[15] := G (ai0 * F b.[3] + ai1 * F b.[7] + ai2 * F b.[11] + ai3 * F b.[15])
  in
    array_ptr_copy_tsz (!p, b, size1_of_int1 16, sizeof<GLfloat>)
  end // end of [go]
in
  go (m, n)
end // end of [mat_mult]

(* ****** ****** *)

implement mat_rot (m, a, x, y, z) = let
  fn go (
      m: &GLmat4, a: GLfloat, x: GLfloat, y: GLfloat, z: GLfloat
    ) :<> void = let
    val a = float_of a
    val x = float_of x and y = float_of y and z = float_of z
    val s = sinf a and c = cosf a
    #define G GLfloat
    var !p_r = @[GLfloat](
      G (x * x * (1.0f - c) + c),     G (y * x * (1.0f - c) + z * s), G (x * z * (1.0f - c) - y * s), G 0.0f,
      G (x * y * (1.0f - c) - z * s), G (y * y * (1.0f - c) + c),     G (y * z * (1.0f - c) + x * s), G 0.0f, 
      G (x * z * (1.0f - c) + y * s), G (y * z * (1.0f - c) - x * s), G (z * z * (1.0f - c) + c), G 0.0f,
      G 0.0f, G 0.0f, G 0.0f, G 1.0f
    ) // end of [var]
  in
    mat_mult (m, !p_r)
  end // end of [go]
in
  go (m, a, x, y, z)
end // end of [mat_rot]

(* ****** ****** *)

implement mat_trn (m, x, y, z) = let
  fn go (m: &GLmat4, x: GLfloat, y: GLfloat, z: GLfloat):<> void = let
    val S = (GLfloat)1.0f and Z = (GLfloat)0.0f
    var !p_t = @[GLfloat](S,Z,Z,Z,  Z,S,Z,Z, Z,Z,S,Z, x,y,z,S)
  in
    mat_mult (m, !p_t)
  end // end of [go]
in
  go (m, x, y, z)
end // end of [mat_trn]

(* ****** ****** *)

absviewtype arrinit_vt (a:viewt@ype, m:int, n:int, l:addr)

extern
fun arrinit_ptr_start {a:viewt@ype} {n:nat} {l:addr} (
  pf_arr: array_v (a?, n, l) | p_arr: ptr l
) :<> arrinit_vt (a, n, 0, l)

extern
fun{a:viewt@ype} arrinit_ptr_extend {m:nat} {n:nat | n < m} {l:addr} (
 ai: arrinit_vt (a, m, n, l)
, x: a
) :<> arrinit_vt (a, m, n+1, l)

extern
fun arrinit_ptr_end {a:viewt@ype} {n:nat} {l:addr} (
  ai: arrinit_vt (a, n, n, l)
) :<> (array_v (a, n, l) | void)

local

assume arrinit_vt (
  a:viewt@ype
, m:int
, n:int
, l:addr
) = [n <= m] [ofs:int] @{
  pf_ini= array_v (a, n, l) // array_v (a, n, l+ofs)
, pf_mul= MUL (n, sizeof a, ofs) // MUL (m-n, sizeof a, ofs)
, pf_rst= array_v (a?, m-n, l+ofs) // array_v (a?, m-n, l)
, p_rst= ptr (l+ofs)
} // end of [assume]

in // in of [local]

implement arrinit_ptr_start {a} {n} {l} (pf_arr | p_arr) = @{
  pf_ini= array_v_nil {a} ()
, pf_mul= mul_make {0,sizeof a} ()
, pf_rst= pf_arr
, p_rst= p_arr
} // end of [arrinit_ptr_start]

implement{a} arrinit_ptr_extend {m} {n} {l} (ai, x) = let
  prval (pf_at, pf_rst) = array_v_uncons {a?} (ai.pf_rst)
  var p = ai.p_rst
  val () = !p := x
in  @{
  pf_ini= array_v_extend {a} (ai.pf_mul, ai.pf_ini, pf_at)
, pf_mul= MULind (ai.pf_mul)
, pf_rst= pf_rst
, p_rst= p + sizeof<a>
}
end // end of [arrinit_ptr_extend]

implement arrinit_ptr_end {a} {n} {l} (ai) = let
  prval () = array_v_unnil {a?} (ai.pf_rst)
in
  (ai.pf_ini | ())
end // end of [arrinit_ptr_end]

end // end of [local]

implement mat_persp (fovy, aspect, near, far, m) = let
  fn go (
      fovy: float, aspect: float, near: float, far: float
    , m: &GLmat4? >> GLmat4
    ):<> void = let
    val ymax = near * tanf (fovy * float_of M_PI / 180.0f)
    val ymin = ~ymax
    val xmin = ymin * aspect
    val xmax = ymax * aspect
    val Z = GLfloat 0.0f
    #define G GLfloat_of_float
    infixl *.
    #define *. arrinit_ptr_extend
    val (pf_ai | ()) = arrinit_ptr_end (arrinit_ptr_start {GLfloat} (view@ m | &m)
           *. G ((2.0f * near) / (xmax - xmin)) *. Z *. Z *. Z
           *. Z *. G ((2.0f * near) / (ymax - ymin)) *. Z *. Z
           *. G ((xmax + xmin) / (xmax - xmin)) *. G ((ymax + ymin) / (ymax - ymin)) *. G (~(far + near) / (far - near)) *. G ~1.0f
           *. Z *. Z *. G (~(2.0f * far * near) / (far - near)) *. G 1.0f)
    prval () = view@ m := pf_ai
  in
    // nothing
  end // end of [go]
in
  go (fovy, aspect, near, far, m)
end // end of [mat_persp]

(* ****** ****** *)

(* end of [mat4.dats] *)
