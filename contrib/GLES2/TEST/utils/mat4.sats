//
// Author: Artyom Shakhakov (artyom DOT shalkhakov AT gmail DOT com)
// Time: June, 2011
//
(*
** Miscellaneous matrix-related functions for use with OpenGL ES.
*)
(* ****** ****** *)

staload "contrib/GLES2/SATS/gl2.sats"

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no staloading at run-time

(* ****** ****** *)

typedef GLmat4 = @[GLfloat][16]

// multiplication of two matrices (in-place)
fun mat_mult (m: &GLmat4, n: &GLmat4):<> void

// concatenate a rotation about arbitrary axis
// given by (x,y,z) by angle [a] onto [m]
fun mat_rot (
  m: &GLmat4, a: GLfloat, x: GLfloat, y: GLfloat, z: GLfloat
) :<> void

// concatenate a translation by (x,y,z) onto [m]
fun mat_trn (m: &GLmat4, x: GLfloat, y: GLfloat, z: GLfloat):<> void

// [m] becomes a perspective projection matrix
fun mat_persp (
  fovy: float, aspect: float, near: float, far: float
, m: &GLmat4? >> GLmat4
) :<> void

(* ****** ****** *)

(* end of [mat4.sats] *)
