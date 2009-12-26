(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: Summer, 2008

(* ****** ****** *)

%{#
#include "contrib/GL/CATS/gl.cats"
%}

(* ****** ****** *)

typedef GLvoid = void

abst@ype GLenum = $extype "ats_GLenum_type" // typedef GLenum = uint
abst@ype GLboolean = $extype "ats_GLboolean_type" // typedef GLboolean = uchar
abst@ype GLbitfield = $extype "ats_GLbitfield_type" // typedef GLbitfield = int
abst@ype GLbyte = $extype "ats_GLbyte_type" // typedef GLbyte = char // 1-byte signed
abst@ype GLubyte = $extype "ats_GLubyte_type" // typedef GLubyte = uchar // 1-byte unsigned
abst@ype GLshort = $extype "ats_GLshort_type" // typedef GLshort = short // 2-byte signed
abst@ype GLushort = $extype "ats_GLushort_type" // typedef GLushort = usint // 2-byte unsigned
abst@ype GLint = $extype "ats_GLint_type" // typedef GLint = int // 4-byte signed
abst@ype GLuint = $extype "ats_GLuint_type" // typedef GLuint = uint // 4-byte unsigned
abst@ype GLsizei = $extype "ats_GLsizei_type" // typedef GLsizei = int // 4-byte signed
abst@ype GLfloat = $extype "ats_GLfloat_type" // typedef GLfloat = float // single precision float
abst@ype GLclampf = $extype "ats_GLclampf_type" // typedef GLclampf = float // single precision float in [0,1]
abst@ype GLdouble = $extype "ats_GLdouble_type" // typedef GLdouble = double // double precision float
abst@ype GLclampd = $extype "ats_GLclampd_type" // typedef GLclampd = double // double precision float in [0,1]

(* ****** ****** *)

fun int_of_GLenum (x: GLenum): int = "atsctrb_int_of_GLenum"

fun GLint_of_int (x: int): GLint = "atsctrb_GLint_of_int"
fun GLfloat_of_double (x: double): GLfloat = "atsctrb_GLfloat_of_double"
fun GLsizei_of_int (x: int): GLsizei = "atsctrb_GLsizei_of_int"

fun lor_GLbitfield_GLbitfield (b1: GLbitfield, b2: GLbitfield): GLbitfield
  = "atsctrb_lor_GLbitfield_GLbitfield"
overload lor with lor_GLbitfield_GLbitfield

(* ****** ****** *)

// Datatypes
macdef GL_BYTE = $extval (GLenum, "GL_BYTE")
macdef GL_UNSIGNED_BYTE = $extval (GLenum, "GL_UNSIGNED_BYTE")
macdef GL_SHORT = $extval (GLenum, "GL_SHORT")
macdef GL_UNSIGNED_SHORT = $extval (GLenum, "GL_UNSIGNED_SHORT")
macdef GL_INT = $extval (GLenum, "GL_INT")
macdef GL_UNSIGNED_INT = $extval (GLenum, "GL_UNSIGNED_INT")
macdef GL_FLOAT = $extval (GLenum, "GL_FLOAT")
macdef GL_2_BYTES = $extval (GLenum, "GL_2_BYTES")
macdef GL_3_BYTES = $extval (GLenum, "GL_3_BYTES")
macdef GL_4_BYTES = $extval (GLenum, "GL_4_BYTES")
macdef GL_DOUBLE = $extval (GLenum, "GL_DOUBLE")

// Boolean values
macdef GL_TRUE = $extval (GLboolean, "GL_TRUE")
macdef GL_FALSE = $extval (GLboolean, "GL_FALSE")

(* ****** ****** *)

// Primitives

macdef GL_POINTS = $extval (GLenum, "GL_POINTS")
macdef GL_LINES = $extval (GLenum, "GL_LINES")
macdef GL_LINE_LOOP = $extval (GLenum, "GL_LINE_LOOP")
macdef GL_LINE_STRIP = $extval (GLenum, "GL_LINE_STRIP")
macdef GL_TRIANGLES = $extval (GLenum, "GL_TRIANGLES")
macdef GL_TRIANGLE_STRIP = $extval (GLenum, "GL_TRIANGLE_STRIP")
macdef GL_TRIANGLE_FAN = $extval (GLenum, "GL_TRIANGLE_FAN")
macdef GL_QUADS = $extval (GLenum, "GL_QUADS")
macdef GL_QUAD_STRIP = $extval (GLenum, "GL_QUAD_STRIP")
macdef GL_POLYGON = $extval (GLenum, "GL_POLYGON")

// Vertex Arrays

macdef GL_VERTEX_ARRAY = $extval (GLenum, "GL_VERTEX_ARRAY")
macdef GL_NORMAL_ARRAY = $extval (GLenum, "GL_NORMAL_ARRAY")
macdef GL_COLOR_ARRAY = $extval (GLenum, "GL_COLOR_ARRAY")
macdef GL_INDEX_ARRAY = $extval (GLenum, "GL_INDEX_ARRAY")
macdef GL_TEXTURE_COORD_ARRAY = $extval (GLenum, "GL_TEXTURE_COORD_ARRAY")
macdef GL_EDGE_FLAG_ARRAY = $extval (GLenum, "GL_EDGE_FLAG_ARRAY")
macdef GL_VERTEX_ARRAY_SIZE = $extval (GLenum, "GL_VERTEX_ARRAY_SIZE")
macdef GL_VERTEX_ARRAY_TYPE = $extval (GLenum, "GL_VERTEX_ARRAY_TYPE")
macdef GL_VERTEX_ARRAY_STRIDE = $extval (GLenum, "GL_VERTEX_ARRAY_STRIDE")
macdef GL_NORMAL_ARRAY_TYPE = $extval (GLenum, "GL_NORMAL_ARRAY_TYPE")
macdef GL_NORMAL_ARRAY_STRIDE = $extval (GLenum, "GL_NORMAL_ARRAY_STRIDE")
macdef GL_COLOR_ARRAY_SIZE = $extval (GLenum, "GL_COLOR_ARRAY_SIZE")
macdef GL_COLOR_ARRAY_TYPE = $extval (GLenum, "GL_COLOR_ARRAY_TYPE")
macdef GL_COLOR_ARRAY_STRIDE = $extval (GLenum, "GL_COLOR_ARRAY_STRIDE")
macdef GL_INDEX_ARRAY_TYPE = $extval (GLenum, "GL_INDEX_ARRAY_TYPE")
macdef GL_INDEX_ARRAY_STRIDE = $extval (GLenum, "GL_INDEX_ARRAY_STRIDE")
macdef GL_TEXTURE_COORD_ARRAY_SIZE = $extval (GLenum, "GL_TEXTURE_COORD_ARRAY_SIZE")
macdef GL_TEXTURE_COORD_ARRAY_TYPE = $extval (GLenum, "GL_TEXTURE_COORD_ARRAY_TYPE")
macdef GL_TEXTURE_COORD_ARRAY_STRIDE = $extval (GLenum, "GL_TEXTURE_COORD_ARRAY_STRIDE")
macdef GL_EDGE_FLAG_ARRAY_STRIDE = $extval (GLenum, "GL_EDGE_FLAG_ARRAY_STRIDE")
macdef GL_VERTEX_ARRAY_POINTER = $extval (GLenum, "GL_VERTEX_ARRAY_POINTER")
macdef GL_NORMAL_ARRAY_POINTER = $extval (GLenum, "GL_NORMAL_ARRAY_POINTER")
macdef GL_COLOR_ARRAY_POINTER = $extval (GLenum, "GL_COLOR_ARRAY_POINTER")
macdef GL_INDEX_ARRAY_POINTER = $extval (GLenum, "GL_INDEX_ARRAY_POINTER")
macdef GL_TEXTURE_COORD_ARRAY_POINTER = $extval (GLenum, "GL_TEXTURE_COORD_ARRAY_POINTER")
macdef GL_EDGE_FLAG_ARRAY_POINTER = $extval (GLenum, "GL_EDGE_FLAG_ARRAY_POINTER")
macdef GL_V2F = $extval (GLenum, "GL_V2F")
macdef GL_V3F = $extval (GLenum, "GL_V3F")
macdef GL_C4UB_V2F = $extval (GLenum, "GL_C4UB_V2F")
macdef GL_C4UB_V3F = $extval (GLenum, "GL_C4UB_V3F")
macdef GL_C3F_V3F = $extval (GLenum, "GL_C3F_V3F")
macdef GL_N3F_V3F = $extval (GLenum, "GL_N3F_V3F")
macdef GL_C4F_N3F_V3F = $extval (GLenum, "GL_C4F_N3F_V3F")
macdef GL_T2F_V3F = $extval (GLenum, "GL_T2F_V3F")
macdef GL_T4F_V4F = $extval (GLenum, "GL_T4F_V4F")
macdef GL_T2F_C4UB_V3F = $extval (GLenum, "GL_T2F_C4UB_V3F")
macdef GL_T2F_C3F_V3F = $extval (GLenum, "GL_T2F_C3F_V3F")
macdef GL_T2F_N3F_V3F = $extval (GLenum, "GL_T2F_N3F_V3F")
macdef GL_T2F_C4F_N3F_V3F = $extval (GLenum, "GL_T2F_C4F_N3F_V3F")
macdef GL_T4F_C4F_N3F_V4F = $extval (GLenum, "GL_T4F_C4F_N3F_V4F")

// Matrix Mode
macdef GL_MATRIX_MODE = $extval (GLenum, "GL_MATRIX_MODE")
macdef GL_MODELVIEW = $extval (GLenum, "GL_MODELVIEW")
macdef GL_PROJECTION = $extval (GLenum, "GL_PROJECTION")
macdef GL_TEXTURE = $extval (GLenum, "GL_TEXTURE")

// Points
macdef GL_POINT_SMOOTH = $extval (GLenum, "GL_POINT_SMOOTH")
macdef GL_POINT_SIZE = $extval (GLenum, "GL_POINT_SIZE")
macdef GL_POINT_SIZE_GRANULARITY = $extval (GLenum, "GL_POINT_SIZE_GRANULARITY")
macdef GL_POINT_SIZE_RANGE = $extval (GLenum, "GL_POINT_SIZE_RANGE")

// Lines
macdef GL_LINE_SMOOTH = $extval (GLenum, "GL_LINE_SMOOTH")
macdef GL_LINE_STIPPLE = $extval (GLenum, "GL_LINE_STIPPLE")
macdef GL_LINE_STIPPLE_PATTERN = $extval (GLenum, "GL_LINE_STIPPLE_PATTERN")
macdef GL_LINE_STIPPLE_REPEAT = $extval (GLenum, "GL_LINE_STIPPLE_REPEAT")
macdef GL_LINE_WIDTH = $extval (GLenum, "GL_LINE_WIDTH")
macdef GL_LINE_WIDTH_GRANULARITY = $extval (GLenum, "GL_LINE_WIDTH_GRANULARITY")
macdef GL_LINE_WIDTH_RANGE = $extval (GLenum, "GL_LINE_WIDTH_RANGE")

// Polygons
macdef GL_POINT = $extval (GLenum, "GL_POINT")
macdef GL_LINE = $extval (GLenum, "GL_LINE")
macdef GL_FILL = $extval (GLenum, "GL_FILL")
macdef GL_CW = $extval (GLenum, "GL_CW")
macdef GL_CCW = $extval (GLenum, "GL_CCW")
macdef GL_FRONT = $extval (GLenum, "GL_FRONT")
macdef GL_BACK = $extval (GLenum, "GL_BACK")
macdef GL_POLYGON_MODE = $extval (GLenum, "GL_POLYGON_MODE")
macdef GL_POLYGON_SMOOTH = $extval (GLenum, "GL_POLYGON_SMOOTH")
macdef GL_POLYGON_STIPPLE = $extval (GLenum, "GL_POLYGON_STIPPLE")
macdef GL_EDGE_FLAG = $extval (GLenum, "GL_EDGE_FLAG")
macdef GL_CULL_FACE = $extval (GLenum, "GL_CULL_FACE")
macdef GL_CULL_FACE_MODE = $extval (GLenum, "GL_CULL_FACE_MODE")
macdef GL_FRONT_FACE = $extval (GLenum, "GL_FRONT_FACE")
macdef GL_POLYGON_OFFSET_FACTOR = $extval (GLenum, "GL_POLYGON_OFFSET_FACTOR")
macdef GL_POLYGON_OFFSET_UNITS = $extval (GLenum, "GL_POLYGON_OFFSET_UNITS")
macdef GL_POLYGON_OFFSET_POINT = $extval (GLenum, "GL_POLYGON_OFFSET_POINT")
macdef GL_POLYGON_OFFSET_LINE = $extval (GLenum, "GL_POLYGON_OFFSET_LINE")
macdef GL_POLYGON_OFFSET_FILL = $extval (GLenum, "GL_POLYGON_OFFSET_FILL")

// Display Lists
macdef GL_COMPILE = $extval (GLenum, "GL_COMPILE")
macdef GL_COMPILE_AND_EXECUTE = $extval (GLenum, "GL_COMPILE_AND_EXECUTE")
macdef GL_LIST_BASE = $extval (GLenum, "GL_LIST_BASE")
macdef GL_LIST_INDEX = $extval (GLenum, "GL_LIST_INDEX")
macdef GL_LIST_MODE = $extval (GLenum, "GL_LIST_MODE")

// Depth buffer
macdef GL_NEVER = $extval (GLenum, "GL_NEVER")
macdef GL_LESS = $extval (GLenum, "GL_LESS")
macdef GL_EQUAL = $extval (GLenum, "GL_EQUAL")
macdef GL_LEQUAL = $extval (GLenum, "GL_LEQUAL")
macdef GL_GREATER = $extval (GLenum, "GL_GREATER")
macdef GL_NOTEQUAL = $extval (GLenum, "GL_NOTEQUAL")
macdef GL_GEQUAL = $extval (GLenum, "GL_GEQUAL")
macdef GL_ALWAYS = $extval (GLenum, "GL_ALWAYS")
macdef GL_DEPTH_TEST = $extval (GLenum, "GL_DEPTH_TEST")
macdef GL_DEPTH_BITS = $extval (GLenum, "GL_DEPTH_BITS")
macdef GL_DEPTH_CLEAR_VALUE = $extval (GLenum, "GL_DEPTH_CLEAR_VALUE")
macdef GL_DEPTH_FUNC = $extval (GLenum, "GL_DEPTH_FUNC")
macdef GL_DEPTH_RANGE = $extval (GLenum, "GL_DEPTH_RANGE")
macdef GL_DEPTH_WRITEMASK = $extval (GLenum, "GL_DEPTH_WRITEMASK")
macdef GL_DEPTH_COMPONENT = $extval (GLenum, "GL_DEPTH_COMPONENT")

// Lighting
macdef GL_LIGHTING = $extval (GLenum, "GL_LIGHTING")
macdef GL_LIGHT0 = $extval (GLenum, "GL_LIGHT0")
macdef GL_LIGHT1 = $extval (GLenum, "GL_LIGHT1")
macdef GL_LIGHT2 = $extval (GLenum, "GL_LIGHT2")
macdef GL_LIGHT3 = $extval (GLenum, "GL_LIGHT3")
macdef GL_LIGHT4 = $extval (GLenum, "GL_LIGHT4")
macdef GL_LIGHT5 = $extval (GLenum, "GL_LIGHT5")
macdef GL_LIGHT6 = $extval (GLenum, "GL_LIGHT6")
macdef GL_LIGHT7 = $extval (GLenum, "GL_LIGHT7")
macdef GL_SPOT_EXPONENT = $extval (GLenum, "GL_SPOT_EXPONENT")
macdef GL_SPOT_CUTOFF = $extval (GLenum, "GL_SPOT_CUTOFF")
macdef GL_CONSTANT_ATTENUATION = $extval (GLenum, "GL_CONSTANT_ATTENUATION")
macdef GL_LINEAR_ATTENUATION = $extval (GLenum, "GL_LINEAR_ATTENUATION")
macdef GL_QUADRATIC_ATTENUATION = $extval (GLenum, "GL_QUADRATIC_ATTENUATION")
macdef GL_AMBIENT = $extval (GLenum, "GL_AMBIENT")
macdef GL_DIFFUSE = $extval (GLenum, "GL_DIFFUSE")
macdef GL_SPECULAR = $extval (GLenum, "GL_SPECULAR")
macdef GL_SHININESS = $extval (GLenum, "GL_SHININESS")
macdef GL_EMISSION = $extval (GLenum, "GL_EMISSION")
macdef GL_POSITION = $extval (GLenum, "GL_POSITION")
macdef GL_SPOT_DIRECTION = $extval (GLenum, "GL_SPOT_DIRECTION")
macdef GL_AMBIENT_AND_DIFFUSE = $extval (GLenum, "GL_AMBIENT_AND_DIFFUSE")
macdef GL_COLOR_INDEXES = $extval (GLenum, "GL_COLOR_INDEXES")
macdef GL_LIGHT_MODEL_TWO_SIDE = $extval (GLenum, "GL_LIGHT_MODEL_TWO_SIDE")
macdef GL_LIGHT_MODEL_LOCAL_VIEWER = $extval (GLenum, "GL_LIGHT_MODEL_LOCAL_VIEWER")
macdef GL_LIGHT_MODEL_AMBIENT = $extval (GLenum, "GL_LIGHT_MODEL_AMBIENT")
macdef GL_FRONT_AND_BACK = $extval (GLenum, "GL_FRONT_AND_BACK")
macdef GL_SHADE_MODEL = $extval (GLenum, "GL_SHADE_MODEL")
macdef GL_FLAT = $extval (GLenum, "GL_FLAT")
macdef GL_SMOOTH = $extval (GLenum, "GL_SMOOTH")
macdef GL_COLOR_MATERIAL = $extval (GLenum, "GL_COLOR_MATERIAL")
macdef GL_COLOR_MATERIAL_FACE = $extval (GLenum, "GL_COLOR_MATERIAL_FACE")
macdef GL_COLOR_MATERIAL_PARAMETER = $extval (GLenum, "GL_COLOR_MATERIAL_PARAMETER")
macdef GL_NORMALIZE = $extval (GLenum, "GL_NORMALIZE")

// User clipping planes
macdef GL_CLIP_PLANE0 = $extval (GLenum, "GL_CLIP_PLANE0")
macdef GL_CLIP_PLANE1 = $extval (GLenum, "GL_CLIP_PLANE1")
macdef GL_CLIP_PLANE2 = $extval (GLenum, "GL_CLIP_PLANE2")
macdef GL_CLIP_PLANE3 = $extval (GLenum, "GL_CLIP_PLANE3")
macdef GL_CLIP_PLANE4 = $extval (GLenum, "GL_CLIP_PLANE4")
macdef GL_CLIP_PLANE5 = $extval (GLenum, "GL_CLIP_PLANE5")

// Accumulation buffer
macdef GL_ACCUM_RED_BITS = $extval (GLenum, "GL_ACCUM_RED_BITS")
macdef GL_ACCUM_GREEN_BITS = $extval (GLenum, "GL_ACCUM_GREEN_BITS")
macdef GL_ACCUM_BLUE_BITS = $extval (GLenum, "GL_ACCUM_BLUE_BITS")
macdef GL_ACCUM_ALPHA_BITS = $extval (GLenum, "GL_ACCUM_ALPHA_BITS")
macdef GL_ACCUM_CLEAR_VALUE = $extval (GLenum, "GL_ACCUM_CLEAR_VALUE")
macdef GL_ACCUM = $extval (GLenum, "GL_ACCUM")
macdef GL_ADD = $extval (GLenum, "GL_ADD")
macdef GL_LOAD = $extval (GLenum, "GL_LOAD")
macdef GL_MULT = $extval (GLenum, "GL_MULT")
macdef GL_RETURN = $extval (GLenum, "GL_RETURN")

// Alpha testing
macdef GL_ALPHA_TEST = $extval (GLenum, "GL_ALPHA_TEST")
macdef GL_ALPHA_TEST_REF = $extval (GLenum, "GL_ALPHA_TEST_REF")
macdef GL_ALPHA_TEST_FUNC = $extval (GLenum, "GL_ALPHA_TEST_FUNC")

// Blending
macdef GL_BLEND = $extval (GLenum, "GL_BLEND")
macdef GL_BLEND_SRC = $extval (GLenum, "GL_BLEND_SRC")
macdef GL_BLEND_DST = $extval (GLenum, "GL_BLEND_DST")
macdef GL_ZERO = $extval (GLenum, "GL_ZERO")
macdef GL_ONE = $extval (GLenum, "GL_ONE")
macdef GL_SRC_COLOR = $extval (GLenum, "GL_SRC_COLOR")
macdef GL_ONE_MINUS_SRC_COLOR = $extval (GLenum, "GL_ONE_MINUS_SRC_COLOR")
macdef GL_SRC_ALPHA = $extval (GLenum, "GL_SRC_ALPHA")
macdef GL_ONE_MINUS_SRC_ALPHA = $extval (GLenum, "GL_ONE_MINUS_SRC_ALPHA")
macdef GL_DST_ALPHA = $extval (GLenum, "GL_DST_ALPHA")
macdef GL_ONE_MINUS_DST_ALPHA = $extval (GLenum, "GL_ONE_MINUS_DST_ALPHA")
macdef GL_DST_COLOR = $extval (GLenum, "GL_DST_COLOR")
macdef GL_ONE_MINUS_DST_COLOR = $extval (GLenum, "GL_ONE_MINUS_DST_COLOR")
macdef GL_SRC_ALPHA_SATURATE = $extval (GLenum, "GL_SRC_ALPHA_SATURATE")

// Render mode
macdef GL_FEEDBACK = $extval (GLenum, "GL_FEEDBACK")
macdef GL_RENDER = $extval (GLenum, "GL_RENDER")
macdef GL_SELECT = $extval (GLenum, "GL_SELECT")

// Feedback
macdef GL_2D = $extval (GLenum, "GL_2D")
macdef GL_3D = $extval (GLenum, "GL_3D")
macdef GL_3D_COLOR = $extval (GLenum, "GL_3D_COLOR")
macdef GL_3D_COLOR_TEXTURE = $extval (GLenum, "GL_3D_COLOR_TEXTURE")
macdef GL_4D_COLOR_TEXTURE = $extval (GLenum, "GL_4D_COLOR_TEXTURE")
macdef GL_POINT_TOKEN = $extval (GLenum, "GL_POINT_TOKEN")
macdef GL_LINE_TOKEN = $extval (GLenum, "GL_LINE_TOKEN")
macdef GL_LINE_RESET_TOKEN = $extval (GLenum, "GL_LINE_RESET_TOKEN")
macdef GL_POLYGON_TOKEN = $extval (GLenum, "GL_POLYGON_TOKEN")
macdef GL_BITMAP_TOKEN = $extval (GLenum, "GL_BITMAP_TOKEN")
macdef GL_DRAW_PIXEL_TOKEN = $extval (GLenum, "GL_DRAW_PIXEL_TOKEN")
macdef GL_COPY_PIXEL_TOKEN = $extval (GLenum, "GL_COPY_PIXEL_TOKEN")
macdef GL_PASS_THROUGH_TOKEN = $extval (GLenum, "GL_PASS_THROUGH_TOKEN")
macdef GL_FEEDBACK_BUFFER_POINTER = $extval (GLenum, "GL_FEEDBACK_BUFFER_POINTER")
macdef GL_FEEDBACK_BUFFER_SIZE = $extval (GLenum, "GL_FEEDBACK_BUFFER_SIZE")
macdef GL_FEEDBACK_BUFFER_TYPE = $extval (GLenum, "GL_FEEDBACK_BUFFER_TYPE")

// Selection
macdef GL_SELECTION_BUFFER_POINTER = $extval (GLenum, "GL_SELECTION_BUFFER_POINTER")
macdef GL_SELECTION_BUFFER_SIZE = $extval (GLenum, "GL_SELECTION_BUFFER_SIZE")

// Fog
macdef GL_FOG = $extval (GLenum, "GL_FOG")
macdef GL_FOG_MODE = $extval (GLenum, "GL_FOG_MODE")
macdef GL_FOG_DENSITY = $extval (GLenum, "GL_FOG_DENSITY")
macdef GL_FOG_COLOR = $extval (GLenum, "GL_FOG_COLOR")
macdef GL_FOG_INDEX = $extval (GLenum, "GL_FOG_INDEX")
macdef GL_FOG_START = $extval (GLenum, "GL_FOG_START")
macdef GL_FOG_END = $extval (GLenum, "GL_FOG_END")
macdef GL_LINEAR = $extval (GLenum, "GL_LINEAR")
macdef GL_EXP = $extval (GLenum, "GL_EXP")
macdef GL_EXP2 = $extval (GLenum, "GL_EXP2")

// Logic Ops
macdef GL_LOGIC_OP = $extval (GLenum, "GL_LOGIC_OP")
macdef GL_INDEX_LOGIC_OP = $extval (GLenum, "GL_INDEX_LOGIC_OP")
macdef GL_COLOR_LOGIC_OP = $extval (GLenum, "GL_COLOR_LOGIC_OP")
macdef GL_LOGIC_OP_MODE = $extval (GLenum, "GL_LOGIC_OP_MODE")
macdef GL_CLEAR = $extval (GLenum, "GL_CLEAR")
macdef GL_SET = $extval (GLenum, "GL_SET")
macdef GL_COPY = $extval (GLenum, "GL_COPY")
macdef GL_COPY_INVERTED = $extval (GLenum, "GL_COPY_INVERTED")
macdef GL_NOOP = $extval (GLenum, "GL_NOOP")
macdef GL_INVERT = $extval (GLenum, "GL_INVERT")
macdef GL_AND = $extval (GLenum, "GL_AND")
macdef GL_NAND = $extval (GLenum, "GL_NAND")
macdef GL_OR = $extval (GLenum, "GL_OR")
macdef GL_NOR = $extval (GLenum, "GL_NOR")
macdef GL_XOR = $extval (GLenum, "GL_XOR")
macdef GL_EQUIV = $extval (GLenum, "GL_EQUIV")
macdef GL_AND_REVERSE = $extval (GLenum, "GL_AND_REVERSE")
macdef GL_AND_INVERTED = $extval (GLenum, "GL_AND_INVERTED")
macdef GL_OR_REVERSE = $extval (GLenum, "GL_OR_REVERSE")
macdef GL_OR_INVERTED = $extval (GLenum, "GL_OR_INVERTED")

// Stencil
macdef GL_STENCIL_BITS = $extval (GLenum, "GL_STENCIL_BITS")
macdef GL_STENCIL_TEST = $extval (GLenum, "GL_STENCIL_TEST")
macdef GL_STENCIL_CLEAR_VALUE = $extval (GLenum, "GL_STENCIL_CLEAR_VALUE")
macdef GL_STENCIL_FUNC = $extval (GLenum, "GL_STENCIL_FUNC")
macdef GL_STENCIL_VALUE_MASK = $extval (GLenum, "GL_STENCIL_VALUE_MASK")
macdef GL_STENCIL_FAIL = $extval (GLenum, "GL_STENCIL_FAIL")
macdef GL_STENCIL_PASS_DEPTH_FAIL = $extval (GLenum, "GL_STENCIL_PASS_DEPTH_FAIL")
macdef GL_STENCIL_PASS_DEPTH_PASS = $extval (GLenum, "GL_STENCIL_PASS_DEPTH_PASS")
macdef GL_STENCIL_REF = $extval (GLenum, "GL_STENCIL_REF")
macdef GL_STENCIL_WRITEMASK = $extval (GLenum, "GL_STENCIL_WRITEMASK")
macdef GL_STENCIL_INDEX = $extval (GLenum, "GL_STENCIL_INDEX")
macdef GL_KEEP = $extval (GLenum, "GL_KEEP")
macdef GL_REPLACE = $extval (GLenum, "GL_REPLACE")
macdef GL_INCR = $extval (GLenum, "GL_INCR")
macdef GL_DECR = $extval (GLenum, "GL_DECR")

// Buffers, Pixel Drawing/Reading
macdef GL_NONE = $extval (GLenum, "GL_NONE")
macdef GL_LEFT = $extval (GLenum, "GL_LEFT")
macdef GL_RIGHT = $extval (GLenum, "GL_RIGHT")
macdef GL_FRONT_LEFT = $extval (GLenum, "GL_FRONT_LEFT")
macdef GL_FRONT_RIGHT = $extval (GLenum, "GL_FRONT_RIGHT")
macdef GL_BACK_LEFT = $extval (GLenum, "GL_BACK_LEFT")
macdef GL_BACK_RIGHT = $extval (GLenum, "GL_BACK_RIGHT")
macdef GL_AUX0 = $extval (GLenum, "GL_AUX0")
macdef GL_AUX1 = $extval (GLenum, "GL_AUX1")
macdef GL_AUX2 = $extval (GLenum, "GL_AUX2")
macdef GL_AUX3 = $extval (GLenum, "GL_AUX3")
macdef GL_COLOR_INDEX = $extval (GLenum, "GL_COLOR_INDEX")
macdef GL_RED = $extval (GLenum, "GL_RED")
macdef GL_GREEN = $extval (GLenum, "GL_GREEN")
macdef GL_BLUE = $extval (GLenum, "GL_BLUE")
macdef GL_ALPHA = $extval (GLenum, "GL_ALPHA")
macdef GL_LUMINANCE = $extval (GLenum, "GL_LUMINANCE")
macdef GL_LUMINANCE_ALPHA = $extval (GLenum, "GL_LUMINANCE_ALPHA")
macdef GL_ALPHA_BITS = $extval (GLenum, "GL_ALPHA_BITS")
macdef GL_RED_BITS = $extval (GLenum, "GL_RED_BITS")
macdef GL_GREEN_BITS = $extval (GLenum, "GL_GREEN_BITS")
macdef GL_BLUE_BITS = $extval (GLenum, "GL_BLUE_BITS")
macdef GL_INDEX_BITS = $extval (GLenum, "GL_INDEX_BITS")
macdef GL_SUBPIXEL_BITS = $extval (GLenum, "GL_SUBPIXEL_BITS")
macdef GL_AUX_BUFFERS = $extval (GLenum, "GL_AUX_BUFFERS")
macdef GL_READ_BUFFER = $extval (GLenum, "GL_READ_BUFFER")
macdef GL_DRAW_BUFFER = $extval (GLenum, "GL_DRAW_BUFFER")
macdef GL_DOUBLEBUFFER = $extval (GLenum, "GL_DOUBLEBUFFER")
macdef GL_STEREO = $extval (GLenum, "GL_STEREO")
macdef GL_BITMAP = $extval (GLenum, "GL_BITMAP")
macdef GL_COLOR = $extval (GLenum, "GL_COLOR")
macdef GL_DEPTH = $extval (GLenum, "GL_DEPTH")
macdef GL_STENCIL = $extval (GLenum, "GL_STENCIL")
macdef GL_DITHER = $extval (GLenum, "GL_DITHER")
macdef GL_RGB = $extval (GLenum, "GL_RGB")
macdef GL_RGBA = $extval (GLenum, "GL_RGBA")

// Implementation Limits
macdef GL_MAX_LIST_NESTING = $extval (GLenum, "GL_MAX_LIST_NESTING")
macdef GL_MAX_EVAL_ORDER = $extval (GLenum, "GL_MAX_EVAL_ORDER")
macdef GL_MAX_LIGHTS = $extval (GLenum, "GL_MAX_LIGHTS")
macdef GL_MAX_CLIP_PLANES = $extval (GLenum, "GL_MAX_CLIP_PLANES")
macdef GL_MAX_TEXTURE_SIZE = $extval (GLenum, "GL_MAX_TEXTURE_SIZE")
macdef GL_MAX_PIXEL_MAP_TABLE = $extval (GLenum, "GL_MAX_PIXEL_MAP_TABLE")
macdef GL_MAX_ATTRIB_STACK_DEPTH = $extval (GLenum, "GL_MAX_ATTRIB_STACK_DEPTH")
macdef GL_MAX_MODELVIEW_STACK_DEPTH = $extval (GLenum, "GL_MAX_MODELVIEW_STACK_DEPTH")
macdef GL_MAX_NAME_STACK_DEPTH = $extval (GLenum, "GL_MAX_NAME_STACK_DEPTH")
macdef GL_MAX_PROJECTION_STACK_DEPTH = $extval (GLenum, "GL_MAX_PROJECTION_STACK_DEPTH")
macdef GL_MAX_TEXTURE_STACK_DEPTH = $extval (GLenum, "GL_MAX_TEXTURE_STACK_DEPTH")
macdef GL_MAX_VIEWPORT_DIMS = $extval (GLenum, "GL_MAX_VIEWPORT_DIMS")
macdef GL_MAX_CLIENT_ATTRIB_STACK_DEPTH = $extval (GLenum, "GL_MAX_CLIENT_ATTRIB_STACK_DEPTH")

// Gets
macdef GL_ATTRIB_STACK_DEPTH = $extval (GLenum, "GL_ATTRIB_STACK_DEPTH")
macdef GL_CLIENT_ATTRIB_STACK_DEPTH = $extval (GLenum, "GL_CLIENT_ATTRIB_STACK_DEPTH")
macdef GL_COLOR_CLEAR_VALUE = $extval (GLenum, "GL_COLOR_CLEAR_VALUE")
macdef GL_COLOR_WRITEMASK = $extval (GLenum, "GL_COLOR_WRITEMASK")
macdef GL_CURRENT_INDEX = $extval (GLenum, "GL_CURRENT_INDEX")
macdef GL_CURRENT_COLOR = $extval (GLenum, "GL_CURRENT_COLOR")
macdef GL_CURRENT_NORMAL = $extval (GLenum, "GL_CURRENT_NORMAL")
macdef GL_CURRENT_RASTER_COLOR = $extval (GLenum, "GL_CURRENT_RASTER_COLOR")
macdef GL_CURRENT_RASTER_DISTANCE = $extval (GLenum, "GL_CURRENT_RASTER_DISTANCE")
macdef GL_CURRENT_RASTER_INDEX = $extval (GLenum, "GL_CURRENT_RASTER_INDEX")
macdef GL_CURRENT_RASTER_POSITION = $extval (GLenum, "GL_CURRENT_RASTER_POSITION")
macdef GL_CURRENT_RASTER_TEXTURE_COORDS = $extval (GLenum, "GL_CURRENT_RASTER_TEXTURE_COORDS")
macdef GL_CURRENT_RASTER_POSITION_VALID = $extval (GLenum, "GL_CURRENT_RASTER_POSITION_VALID")
macdef GL_CURRENT_TEXTURE_COORDS = $extval (GLenum, "GL_CURRENT_TEXTURE_COORDS")
macdef GL_INDEX_CLEAR_VALUE = $extval (GLenum, "GL_INDEX_CLEAR_VALUE")
macdef GL_INDEX_MODE = $extval (GLenum, "GL_INDEX_MODE")
macdef GL_INDEX_WRITEMASK = $extval (GLenum, "GL_INDEX_WRITEMASK")
macdef GL_MODELVIEW_MATRIX = $extval (GLenum, "GL_MODELVIEW_MATRIX")
macdef GL_MODELVIEW_STACK_DEPTH = $extval (GLenum, "GL_MODELVIEW_STACK_DEPTH")
macdef GL_NAME_STACK_DEPTH = $extval (GLenum, "GL_NAME_STACK_DEPTH")
macdef GL_PROJECTION_MATRIX = $extval (GLenum, "GL_PROJECTION_MATRIX")
macdef GL_PROJECTION_STACK_DEPTH = $extval (GLenum, "GL_PROJECTION_STACK_DEPTH")
macdef GL_RENDER_MODE = $extval (GLenum, "GL_RENDER_MODE")
macdef GL_RGBA_MODE = $extval (GLenum, "GL_RGBA_MODE")
macdef GL_TEXTURE_MATRIX = $extval (GLenum, "GL_TEXTURE_MATRIX")
macdef GL_TEXTURE_STACK_DEPTH = $extval (GLenum, "GL_TEXTURE_STACK_DEPTH")
macdef GL_VIEWPORT = $extval (GLenum, "GL_VIEWPORT")

// Evaluators
macdef GL_AUTO_NORMAL = $extval (GLenum, "GL_AUTO_NORMAL")
macdef GL_MAP1_COLOR_4 = $extval (GLenum, "GL_MAP1_COLOR_4")
macdef GL_MAP1_INDEX = $extval (GLenum, "GL_MAP1_INDEX")
macdef GL_MAP1_NORMAL = $extval (GLenum, "GL_MAP1_NORMAL")
macdef GL_MAP1_TEXTURE_COORD_1 = $extval (GLenum, "GL_MAP1_TEXTURE_COORD_1")
macdef GL_MAP1_TEXTURE_COORD_2 = $extval (GLenum, "GL_MAP1_TEXTURE_COORD_2")
macdef GL_MAP1_TEXTURE_COORD_3 = $extval (GLenum, "GL_MAP1_TEXTURE_COORD_3")
macdef GL_MAP1_TEXTURE_COORD_4 = $extval (GLenum, "GL_MAP1_TEXTURE_COORD_4")
macdef GL_MAP1_VERTEX_3 = $extval (GLenum, "GL_MAP1_VERTEX_3")
macdef GL_MAP1_VERTEX_4 = $extval (GLenum, "GL_MAP1_VERTEX_4")
macdef GL_MAP2_COLOR_4 = $extval (GLenum, "GL_MAP2_COLOR_4")
macdef GL_MAP2_INDEX = $extval (GLenum, "GL_MAP2_INDEX")
macdef GL_MAP2_NORMAL = $extval (GLenum, "GL_MAP2_NORMAL")
macdef GL_MAP2_TEXTURE_COORD_1 = $extval (GLenum, "GL_MAP2_TEXTURE_COORD_1")
macdef GL_MAP2_TEXTURE_COORD_2 = $extval (GLenum, "GL_MAP2_TEXTURE_COORD_2")
macdef GL_MAP2_TEXTURE_COORD_3 = $extval (GLenum, "GL_MAP2_TEXTURE_COORD_3")
macdef GL_MAP2_TEXTURE_COORD_4 = $extval (GLenum, "GL_MAP2_TEXTURE_COORD_4")
macdef GL_MAP2_VERTEX_3 = $extval (GLenum, "GL_MAP2_VERTEX_3")
macdef GL_MAP2_VERTEX_4 = $extval (GLenum, "GL_MAP2_VERTEX_4")
macdef GL_MAP1_GRID_DOMAIN = $extval (GLenum, "GL_MAP1_GRID_DOMAIN")
macdef GL_MAP1_GRID_SEGMENTS = $extval (GLenum, "GL_MAP1_GRID_SEGMENTS")
macdef GL_MAP2_GRID_DOMAIN = $extval (GLenum, "GL_MAP2_GRID_DOMAIN")
macdef GL_MAP2_GRID_SEGMENTS = $extval (GLenum, "GL_MAP2_GRID_SEGMENTS")
macdef GL_COEFF = $extval (GLenum, "GL_COEFF")
macdef GL_ORDER = $extval (GLenum, "GL_ORDER")
macdef GL_DOMAIN = $extval (GLenum, "GL_DOMAIN")

// Hints
macdef GL_PERSPECTIVE_CORRECTION_HINT = $extval (GLenum, "GL_PERSPECTIVE_CORRECTION_HINT")
macdef GL_POINT_SMOOTH_HINT = $extval (GLenum, "GL_POINT_SMOOTH_HINT")
macdef GL_LINE_SMOOTH_HINT = $extval (GLenum, "GL_LINE_SMOOTH_HINT")
macdef GL_POLYGON_SMOOTH_HINT = $extval (GLenum, "GL_POLYGON_SMOOTH_HINT")
macdef GL_FOG_HINT = $extval (GLenum, "GL_FOG_HINT")
macdef GL_DONT_CARE = $extval (GLenum, "GL_DONT_CARE")
macdef GL_FASTEST = $extval (GLenum, "GL_FASTEST")
macdef GL_NICEST = $extval (GLenum, "GL_NICEST")

// Scissor box
macdef GL_SCISSOR_BOX = $extval (GLenum, "GL_SCISSOR_BOX")
macdef GL_SCISSOR_TEST = $extval (GLenum, "GL_SCISSOR_TEST")

// Pixel Mode / Transfer
macdef GL_MAP_COLOR = $extval (GLenum, "GL_MAP_COLOR")
macdef GL_MAP_STENCIL = $extval (GLenum, "GL_MAP_STENCIL")
macdef GL_INDEX_SHIFT = $extval (GLenum, "GL_INDEX_SHIFT")
macdef GL_INDEX_OFFSET = $extval (GLenum, "GL_INDEX_OFFSET")
macdef GL_RED_SCALE = $extval (GLenum, "GL_RED_SCALE")
macdef GL_RED_BIAS = $extval (GLenum, "GL_RED_BIAS")
macdef GL_GREEN_SCALE = $extval (GLenum, "GL_GREEN_SCALE")
macdef GL_GREEN_BIAS = $extval (GLenum, "GL_GREEN_BIAS")
macdef GL_BLUE_SCALE = $extval (GLenum, "GL_BLUE_SCALE")
macdef GL_BLUE_BIAS = $extval (GLenum, "GL_BLUE_BIAS")
macdef GL_ALPHA_SCALE = $extval (GLenum, "GL_ALPHA_SCALE")
macdef GL_ALPHA_BIAS = $extval (GLenum, "GL_ALPHA_BIAS")
macdef GL_DEPTH_SCALE = $extval (GLenum, "GL_DEPTH_SCALE")
macdef GL_DEPTH_BIAS = $extval (GLenum, "GL_DEPTH_BIAS")
macdef GL_PIXEL_MAP_S_TO_S_SIZE = $extval (GLenum, "GL_PIXEL_MAP_S_TO_S_SIZE")
macdef GL_PIXEL_MAP_I_TO_I_SIZE = $extval (GLenum, "GL_PIXEL_MAP_I_TO_I_SIZE")
macdef GL_PIXEL_MAP_I_TO_R_SIZE = $extval (GLenum, "GL_PIXEL_MAP_I_TO_R_SIZE")
macdef GL_PIXEL_MAP_I_TO_G_SIZE = $extval (GLenum, "GL_PIXEL_MAP_I_TO_G_SIZE")
macdef GL_PIXEL_MAP_I_TO_B_SIZE = $extval (GLenum, "GL_PIXEL_MAP_I_TO_B_SIZE")
macdef GL_PIXEL_MAP_I_TO_A_SIZE = $extval (GLenum, "GL_PIXEL_MAP_I_TO_A_SIZE")
macdef GL_PIXEL_MAP_R_TO_R_SIZE = $extval (GLenum, "GL_PIXEL_MAP_R_TO_R_SIZE")
macdef GL_PIXEL_MAP_G_TO_G_SIZE = $extval (GLenum, "GL_PIXEL_MAP_G_TO_G_SIZE")
macdef GL_PIXEL_MAP_B_TO_B_SIZE = $extval (GLenum, "GL_PIXEL_MAP_B_TO_B_SIZE")
macdef GL_PIXEL_MAP_A_TO_A_SIZE = $extval (GLenum, "GL_PIXEL_MAP_A_TO_A_SIZE")
macdef GL_PIXEL_MAP_S_TO_S = $extval (GLenum, "GL_PIXEL_MAP_S_TO_S")
macdef GL_PIXEL_MAP_I_TO_I = $extval (GLenum, "GL_PIXEL_MAP_I_TO_I")
macdef GL_PIXEL_MAP_I_TO_R = $extval (GLenum, "GL_PIXEL_MAP_I_TO_R")
macdef GL_PIXEL_MAP_I_TO_G = $extval (GLenum, "GL_PIXEL_MAP_I_TO_G")
macdef GL_PIXEL_MAP_I_TO_B = $extval (GLenum, "GL_PIXEL_MAP_I_TO_B")
macdef GL_PIXEL_MAP_I_TO_A = $extval (GLenum, "GL_PIXEL_MAP_I_TO_A")
macdef GL_PIXEL_MAP_R_TO_R = $extval (GLenum, "GL_PIXEL_MAP_R_TO_R")
macdef GL_PIXEL_MAP_G_TO_G = $extval (GLenum, "GL_PIXEL_MAP_G_TO_G")
macdef GL_PIXEL_MAP_B_TO_B = $extval (GLenum, "GL_PIXEL_MAP_B_TO_B")
macdef GL_PIXEL_MAP_A_TO_A = $extval (GLenum, "GL_PIXEL_MAP_A_TO_A")
macdef GL_PACK_ALIGNMENT = $extval (GLenum, "GL_PACK_ALIGNMENT")
macdef GL_PACK_LSB_FIRST = $extval (GLenum, "GL_PACK_LSB_FIRST")
macdef GL_PACK_ROW_LENGTH = $extval (GLenum, "GL_PACK_ROW_LENGTH")
macdef GL_PACK_SKIP_PIXELS = $extval (GLenum, "GL_PACK_SKIP_PIXELS")
macdef GL_PACK_SKIP_ROWS = $extval (GLenum, "GL_PACK_SKIP_ROWS")
macdef GL_PACK_SWAP_BYTES = $extval (GLenum, "GL_PACK_SWAP_BYTES")
macdef GL_UNPACK_ALIGNMENT = $extval (GLenum, "GL_UNPACK_ALIGNMENT")
macdef GL_UNPACK_LSB_FIRST = $extval (GLenum, "GL_UNPACK_LSB_FIRST")
macdef GL_UNPACK_ROW_LENGTH = $extval (GLenum, "GL_UNPACK_ROW_LENGTH")
macdef GL_UNPACK_SKIP_PIXELS = $extval (GLenum, "GL_UNPACK_SKIP_PIXELS")
macdef GL_UNPACK_SKIP_ROWS = $extval (GLenum, "GL_UNPACK_SKIP_ROWS")
macdef GL_UNPACK_SWAP_BYTES = $extval (GLenum, "GL_UNPACK_SWAP_BYTES")
macdef GL_ZOOM_X = $extval (GLenum, "GL_ZOOM_X")
macdef GL_ZOOM_Y = $extval (GLenum, "GL_ZOOM_Y")

// Texture mapping
macdef GL_TEXTURE_ENV = $extval (GLenum, "GL_TEXTURE_ENV")
macdef GL_TEXTURE_ENV_MODE = $extval (GLenum, "GL_TEXTURE_ENV_MODE")
macdef GL_TEXTURE_1D = $extval (GLenum, "GL_TEXTURE_1D")
macdef GL_TEXTURE_2D = $extval (GLenum, "GL_TEXTURE_2D")
macdef GL_TEXTURE_WRAP_S = $extval (GLenum, "GL_TEXTURE_WRAP_S")
macdef GL_TEXTURE_WRAP_T = $extval (GLenum, "GL_TEXTURE_WRAP_T")
macdef GL_TEXTURE_MAG_FILTER = $extval (GLenum, "GL_TEXTURE_MAG_FILTER")
macdef GL_TEXTURE_MIN_FILTER = $extval (GLenum, "GL_TEXTURE_MIN_FILTER")
macdef GL_TEXTURE_ENV_COLOR = $extval (GLenum, "GL_TEXTURE_ENV_COLOR")
macdef GL_TEXTURE_GEN_S = $extval (GLenum, "GL_TEXTURE_GEN_S")
macdef GL_TEXTURE_GEN_T = $extval (GLenum, "GL_TEXTURE_GEN_T")
macdef GL_TEXTURE_GEN_MODE = $extval (GLenum, "GL_TEXTURE_GEN_MODE")
macdef GL_TEXTURE_BORDER_COLOR = $extval (GLenum, "GL_TEXTURE_BORDER_COLOR")
macdef GL_TEXTURE_WIDTH = $extval (GLenum, "GL_TEXTURE_WIDTH")
macdef GL_TEXTURE_HEIGHT = $extval (GLenum, "GL_TEXTURE_HEIGHT")
macdef GL_TEXTURE_BORDER = $extval (GLenum, "GL_TEXTURE_BORDER")
macdef GL_TEXTURE_COMPONENTS = $extval (GLenum, "GL_TEXTURE_COMPONENTS")
macdef GL_TEXTURE_RED_SIZE = $extval (GLenum, "GL_TEXTURE_RED_SIZE")
macdef GL_TEXTURE_GREEN_SIZE = $extval (GLenum, "GL_TEXTURE_GREEN_SIZE")
macdef GL_TEXTURE_BLUE_SIZE = $extval (GLenum, "GL_TEXTURE_BLUE_SIZE")
macdef GL_TEXTURE_ALPHA_SIZE = $extval (GLenum, "GL_TEXTURE_ALPHA_SIZE")
macdef GL_TEXTURE_LUMINANCE_SIZE = $extval (GLenum, "GL_TEXTURE_LUMINANCE_SIZE")
macdef GL_TEXTURE_INTENSITY_SIZE = $extval (GLenum, "GL_TEXTURE_INTENSITY_SIZE")
macdef GL_NEAREST_MIPMAP_NEAREST = $extval (GLenum, "GL_NEAREST_MIPMAP_NEAREST")
macdef GL_NEAREST_MIPMAP_LINEAR = $extval (GLenum, "GL_NEAREST_MIPMAP_LINEAR")
macdef GL_LINEAR_MIPMAP_NEAREST = $extval (GLenum, "GL_LINEAR_MIPMAP_NEAREST")
macdef GL_LINEAR_MIPMAP_LINEAR = $extval (GLenum, "GL_LINEAR_MIPMAP_LINEAR")
macdef GL_OBJECT_LINEAR = $extval (GLenum, "GL_OBJECT_LINEAR")
macdef GL_OBJECT_PLANE = $extval (GLenum, "GL_OBJECT_PLANE")
macdef GL_EYE_LINEAR = $extval (GLenum, "GL_EYE_LINEAR")
macdef GL_EYE_PLANE = $extval (GLenum, "GL_EYE_PLANE")
macdef GL_SPHERE_MAP = $extval (GLenum, "GL_SPHERE_MAP")
macdef GL_DECAL = $extval (GLenum, "GL_DECAL")
macdef GL_MODULATE = $extval (GLenum, "GL_MODULATE")
macdef GL_NEAREST = $extval (GLenum, "GL_NEAREST")
macdef GL_REPEAT = $extval (GLenum, "GL_REPEAT")
macdef GL_CLAMP = $extval (GLenum, "GL_CLAMP")
macdef GL_S = $extval (GLenum, "GL_S")
macdef GL_T = $extval (GLenum, "GL_T")
macdef GL_R = $extval (GLenum, "GL_R")
macdef GL_Q = $extval (GLenum, "GL_Q")
macdef GL_TEXTURE_GEN_R = $extval (GLenum, "GL_TEXTURE_GEN_R")
macdef GL_TEXTURE_GEN_Q = $extval (GLenum, "GL_TEXTURE_GEN_Q")

// Utility
macdef GL_VENDOR = $extval (GLenum, "GL_VENDOR")
macdef GL_RENDERER = $extval (GLenum, "GL_RENDERER")
macdef GL_VERSION = $extval (GLenum, "GL_VERSION")
macdef GL_EXTENSIONS = $extval (GLenum, "GL_EXTENSIONS")

// Errors
macdef GL_NO_ERROR = $extval (GLenum, "GL_NO_ERROR")
macdef GL_INVALID_ENUM = $extval (GLenum, "GL_INVALID_ENUM")
macdef GL_INVALID_VALUE = $extval (GLenum, "GL_INVALID_VALUE")
macdef GL_INVALID_OPERATION = $extval (GLenum, "GL_INVALID_OPERATION")
macdef GL_STACK_OVERFLOW = $extval (GLenum, "GL_STACK_OVERFLOW")
macdef GL_STACK_UNDERFLOW = $extval (GLenum, "GL_STACK_UNDERFLOW")
macdef GL_OUT_OF_MEMORY = $extval (GLenum, "GL_OUT_OF_MEMORY")

// glPush/PopAttrib bits
macdef GL_CURRENT_BIT = $extval (GLbitfield, "GL_CURRENT_BIT")
macdef GL_POINT_BIT = $extval (GLbitfield, "GL_POINT_BIT")
macdef GL_LINE_BIT = $extval (GLbitfield, "GL_LINE_BIT")
macdef GL_POLYGON_BIT = $extval (GLbitfield, "GL_POLYGON_BIT")
macdef GL_POLYGON_STIPPLE_BIT = $extval (GLbitfield, "GL_POLYGON_STIPPLE_BIT")
macdef GL_PIXEL_MODE_BIT = $extval (GLbitfield, "GL_PIXEL_MODE_BIT")
macdef GL_LIGHTING_BIT = $extval (GLbitfield, "GL_LIGHTING_BIT")
macdef GL_FOG_BIT = $extval (GLbitfield, "GL_FOG_BIT")
macdef GL_DEPTH_BUFFER_BIT = $extval (GLbitfield, "GL_DEPTH_BUFFER_BIT")
macdef GL_ACCUM_BUFFER_BIT = $extval (GLbitfield, "GL_ACCUM_BUFFER_BIT")
macdef GL_STENCIL_BUFFER_BIT = $extval (GLbitfield, "GL_STENCIL_BUFFER_BIT")
macdef GL_VIEWPORT_BIT = $extval (GLbitfield, "GL_VIEWPORT_BIT")
macdef GL_TRANSFORM_BIT = $extval (GLbitfield, "GL_TRANSFORM_BIT")
macdef GL_ENABLE_BIT = $extval (GLbitfield, "GL_ENABLE_BIT")
macdef GL_COLOR_BUFFER_BIT = $extval (GLbitfield, "GL_COLOR_BUFFER_BIT")
macdef GL_HINT_BIT = $extval (GLbitfield, "GL_HINT_BIT")
macdef GL_EVAL_BIT = $extval (GLbitfield, "GL_EVAL_BIT")
macdef GL_LIST_BIT = $extval (GLbitfield, "GL_LIST_BIT")
macdef GL_TEXTURE_BIT = $extval (GLbitfield, "GL_TEXTURE_BIT")
macdef GL_SCISSOR_BIT = $extval (GLbitfield, "GL_SCISSOR_BIT")
macdef GL_ALL_ATTRIB_BITS = $extval (GLbitfield, "GL_ALL_ATTRIB_BITS")

// OpenGL 1.1
macdef GL_PROXY_TEXTURE_1D = $extval (GLenum, "GL_PROXY_TEXTURE_1D")
macdef GL_PROXY_TEXTURE_2D = $extval (GLenum, "GL_PROXY_TEXTURE_2D")
macdef GL_TEXTURE_PRIORITY = $extval (GLenum, "GL_TEXTURE_PRIORITY")
macdef GL_TEXTURE_RESIDENT = $extval (GLenum, "GL_TEXTURE_RESIDENT")
macdef GL_TEXTURE_BINDING_1D = $extval (GLenum, "GL_TEXTURE_BINDING_1D")
macdef GL_TEXTURE_BINDING_2D = $extval (GLenum, "GL_TEXTURE_BINDING_2D")
macdef GL_TEXTURE_INTERNAL_FORMAT = $extval (GLenum, "GL_TEXTURE_INTERNAL_FORMAT")
macdef GL_ALPHA4 = $extval (GLenum, "GL_ALPHA4")
macdef GL_ALPHA8 = $extval (GLenum, "GL_ALPHA8")
macdef GL_ALPHA12 = $extval (GLenum, "GL_ALPHA12")
macdef GL_ALPHA16 = $extval (GLenum, "GL_ALPHA16")
macdef GL_LUMINANCE4 = $extval (GLenum, "GL_LUMINANCE4")
macdef GL_LUMINANCE8 = $extval (GLenum, "GL_LUMINANCE8")
macdef GL_LUMINANCE12 = $extval (GLenum, "GL_LUMINANCE12")
macdef GL_LUMINANCE16 = $extval (GLenum, "GL_LUMINANCE16")
macdef GL_LUMINANCE4_ALPHA4 = $extval (GLenum, "GL_LUMINANCE4_ALPHA4")
macdef GL_LUMINANCE6_ALPHA2 = $extval (GLenum, "GL_LUMINANCE6_ALPHA2")
macdef GL_LUMINANCE8_ALPHA8 = $extval (GLenum, "GL_LUMINANCE8_ALPHA8")
macdef GL_LUMINANCE12_ALPHA4 = $extval (GLenum, "GL_LUMINANCE12_ALPHA4")
macdef GL_LUMINANCE12_ALPHA12 = $extval (GLenum, "GL_LUMINANCE12_ALPHA12")
macdef GL_LUMINANCE16_ALPHA16 = $extval (GLenum, "GL_LUMINANCE16_ALPHA16")
macdef GL_INTENSITY = $extval (GLenum, "GL_INTENSITY")
macdef GL_INTENSITY4 = $extval (GLenum, "GL_INTENSITY4")
macdef GL_INTENSITY8 = $extval (GLenum, "GL_INTENSITY8")
macdef GL_INTENSITY12 = $extval (GLenum, "GL_INTENSITY12")
macdef GL_INTENSITY16 = $extval (GLenum, "GL_INTENSITY16")
macdef GL_R3_G3_B2 = $extval (GLenum, "GL_R3_G3_B2")
macdef GL_RGB4 = $extval (GLenum, "GL_RGB4")
macdef GL_RGB5 = $extval (GLenum, "GL_RGB5")
macdef GL_RGB8 = $extval (GLenum, "GL_RGB8")
macdef GL_RGB10 = $extval (GLenum, "GL_RGB10")
macdef GL_RGB12 = $extval (GLenum, "GL_RGB12")
macdef GL_RGB16 = $extval (GLenum, "GL_RGB16")
macdef GL_RGBA2 = $extval (GLenum, "GL_RGBA2")
macdef GL_RGBA4 = $extval (GLenum, "GL_RGBA4")
macdef GL_RGB5_A1 = $extval (GLenum, "GL_RGB5_A1")
macdef GL_RGBA8 = $extval (GLenum, "GL_RGBA8")
macdef GL_RGB10_A2 = $extval (GLenum, "GL_RGB10_A2")
macdef GL_RGBA12 = $extval (GLenum, "GL_RGBA12")
macdef GL_RGBA16 = $extval (GLenum, "GL_RGBA16")
macdef GL_CLIENT_PIXEL_STORE_BIT = $extval (GLenum, "GL_CLIENT_PIXEL_STORE_BIT")
macdef GL_CLIENT_VERTEX_ARRAY_BIT = $extval (GLenum, "GL_CLIENT_VERTEX_ARRAY_BIT")
macdef GL_ALL_CLIENT_ATTRIB_BITS = $extval (GLenum, "GL_ALL_CLIENT_ATTRIB_BITS")
macdef GL_CLIENT_ALL_ATTRIB_BITS = $extval (GLenum, "GL_CLIENT_ALL_ATTRIB_BITS")

(* ****** ****** *)

// Miscellaneous

fun glClearIndex(c: GLfloat): void = "atsctrb_glClearIndex"


//

symintr glClearColor
fun glClearColor_double
  (red: double, green: double, blue: double, alpha: double): void
  = "atsctrb_glClearColor_double"
fun glClearColor_GLclampf
  (red: GLclampf, green: GLclampf, blue: GLclampf, alpha: GLclampf): void
  = "atsctrb_glClearColor_GLclampf"
overload glClearColor with glClearColor_double
overload glClearColor with glClearColor_GLclampf

//

fun glClear (mask: GLbitfield): void = "atsctrb_glClear"

fun glIndexMask (mask: GLuint): void = "atsctrb_glIndexMask"

fun glColorMask (red: GLboolean, green: GLboolean, blue: GLboolean, alpha: GLboolean): void
  = "atsctrb_glColorMask"

fun glAlphaFunc (func: GLenum, ref: GLclampf): void = "atsctrb_glAlphaFunc"

fun glBlendFunc (sfactor: GLenum, dfactor: GLenum): void = "atsctrb_glBlendFunc"

fun glLogicOp (opcode: GLenum): void = "atsctrb_glLogicOp"

fun glCullFace (mode: GLenum): void = "atsctrb_glCullFace"

fun glFrontFace (mode: GLenum): void  = "atsctrb_glFrontFace"

//

symintr glPointSize
fun glPointSize_double (width: double): void = "atsctrb_glPointSize_double"
fun glPointSize_GLfloat (width: GLfloat): void = "atsctrb_glPointSize_GLfloat"
overload glPointSize with glPointSize_double
overload glPointSize with glPointSize_GLfloat

//

symintr glLineWidth
fun glLineWidth_double (width: double): void = "atsctrb_glLineWidth_double"
fun glLineWidth_GLfloat (width: GLfloat): void = "atsctrb_glLineWidth_GLfloat"
overload glLineWidth with glLineWidth_double
overload glLineWidth with glLineWidth_GLfloat

//

fun glLineStipple (factor: GLint, pattern: GLushort): void = "atsctrb_glLineStipple"

fun glPolygonMode (face: GLenum, mode: GLenum): void = "atsctrb_glPolygonMode"

fun glPolygonOffset (factor: GLfloat, units: GLfloat): void = "atsctrb_glPolygonOffset"

// fun glPolygonStipple (const GLubyte *mask);

// fun glGetPolygonStipple (GLubyte *mask);

fun glEdgeFlag (flag: GLboolean): void = "atsctrb_glEdgeFlag"

// fun glEdgeFlagv ( const GLboolean *flag);

fun glScissor(x: GLint, y: GLint, width: GLsizei, height: GLsizei): void
  = "atsctrb_glScissor"

fun glClipPlane {l:addr}
  (pf: array_v (GLdouble, 4, l) | plane: GLenum, eqn: ptr l): void
  = "atsctrb_glClipPlane"

fun glGetClipPlane {l:addr}
  (pf: array_v (GLdouble?, 4, l) | plane: GLenum, eqn: ptr l): void
  = "atsctrb_glGetClipPlane"

fun glDrawBuffer (mode: GLenum): void = "atsctrb_glDrawBuffer"

fun glReadBuffer (mode: GLenum): void = "atsctrb_glReadBuffer"

fun glEnable (cap: GLenum): void = "atsctrb_glEnable"

fun glDisable (cap: GLenum): void = "atsctrb_glDisable"

fun glIsEnabled (cap: GLenum): GLboolean = "atsctrb_GLboolean"

// version 1.1
fun glEnableClientState (cap: GLenum): void = "atsctrb_glEnableClientState"

// version 1.1
fun glDisableClientState (cap: GLenum): void = "atsctrb_glDisableClientState"

// fun glGetBooleanv (pname: GLenum, GLboolean *params);

// fun glGetDoublev (pname: GLenum, GLdouble *params);

// fun glGetFloatv (pname: GLenum, GLfloat *params);

// fun glGetIntegerv (pname: GLenum, GLint *params);

fun glPushAttrib (mask: GLbitfield): void = "atsctrb_glPushAttrib"

fun glPopAttrib (): void = "atsctrb_glPopAttrib"

// version 1.1
fun glPushClientAttrib (mask: GLbitfield): void = "atsctrb_glPushClientAttrib"

// version 1.1
fun glPopClientAttrib (): void = "atsctrb_glPopClientAttrib"

fun glRenderMode (mode: GLenum): GLint = "atsctrb_glRenderMode"
fun glGetError (): GLenum = "atsctrb_glGetError"

fun glGetString (name: GLenum): string = "atsctrb_glGetString"

fun glFinish (): void = "atsctrb_glFinish"

fun glFlush (): void = "atsctrb_glFlush"

fun glHint (target: GLenum, mode: GLenum): void = "atsctrb_glHint"

(* ****** ****** *)

// Depth Buffer

fun glClearDepth (depth: GLclampd): void = "atsctrb_glClearDepth"

fun glDepthFunc (func: GLenum): void = "atsctrb_glDepthFunc"

fun glDepthMask (flag: GLboolean): void = "atsctrb_glDepthMask"

fun glDepthRange (near_val: GLclampd, far_val: GLclampd): void
  = "atsctrb_glDepthRange"

(* ****** ****** *)

// Accumulation Buffer

fun glClearAccum
  (red: GLfloat, green: GLfloat, blue: GLfloat, alpha: GLfloat): void
  = "atsctrb_glClearAccum"

fun glAccum (opr: GLenum, value: GLfloat): void = "atsctrb_glAccum"

// Transformation

fun glMatrixMode (mode: GLenum): void = "atsctrb_glMatrixMode"

(* ****** ****** *)

typedef glOrtho_type (a:t@ype) = (
  a (*lft*), a (*rgt*)
, a (*bot*), a (*top*)
, a (*near_val*), a (*far_val*)
) -<fun1> void // end of [glOrtho_type]

symintr glOrtho

fun glOrtho_double : glOrtho_type (double)
  = "atsctrb_glOrtho_double"
overload glOrtho with glOrtho_double

fun glOrtho_GLdouble : glOrtho_type (GLdouble)
  = "atsctrb_glOrtho_GLdouble"
overload glOrtho with glOrtho_GLdouble

(* ****** ****** *)

typedef glFrustum_type (a:t@ype) = (
  a (*lft*), a (*rgh*)
, a (*bot*), a (*top*)
, a (*near_val*), a (*far_val*)
) -<fun1> void

symintr glFrustum

fun glFrustum_double : glFrustum_type (double)
  = "atsctrb_glFrustum_double"
overload glFrustum with glFrustum_double

fun glFrustum_GLdouble : glFrustum_type (GLdouble)
  = "atsctrb_glFrustum_GLdouble"
overload glFrustum with glFrustum_GLdouble

(* ****** ****** *)

symintr glViewport
fun glViewport_type (x: int, y: int, width: int, height: int): void
  = "atsctrb_glViewport_type"
fun glViewport_GLtype (x: GLint, y: GLint, width: GLsizei, height: GLsizei): void
  = "atsctrb_glViewport_GLtype"
overload glViewport with glViewport_type
overload glViewport with glViewport_GLtype

//

absview glPushMatrixView
fun glPushMatrix (): (glPushMatrixView | void)
  = "atsctrb_glPushMatrix"
fun glPopMatrix (pf: glPushMatrixView | (*none*)): void
  = "atsctrb_glPopMatrix"

//

fun glLoadIdentity (): void = "atsctrb_glLoadIdentity"

//

fun glLoadMatrixd {l:addr}
  (pf: array_v (GLdouble, 16, l) | p: ptr l): void
  = "atsctrb_glLoadMatrixd"

fun glLoadMatrixf {l:addr}
  (pf: array_v (GLfloat, 16, l) | p: ptr l): void
  = "atsctrb_glLoadMatrixf"

//

fun glMultMatrixd {l:addr}
  (pf: array_v (GLdouble, 16, l) | p: ptr l): void
  = "atsctrb_glMultMatrixd"

fun glMultMatrixf {l:addr}
  (pf: array_v (GLfloat, 16, l) | p: ptr l): void
  = "atsctrb_glMultMatrixf"

(* ****** ****** *)

typedef glRotate_type (a:t@ype) =
  (a(*angle*), a(*x*), a(*y*), a(*z*)) -<fun1> void

symintr glRotated

fun glRotated_double : glRotate_type (double)
  = "atsctrb_glRotated_double"
overload glRotated with glRotated_double

fun glRotated_GLdouble : glRotate_type (GLdouble)
  = "atsctrb_glRotated_GLdouble"
overload glRotated with glRotated_GLdouble

symintr glRotatef

fun glRotatef_double : glRotate_type (double)
  = "atsctrb_glRotatef_double"
overload glRotatef with glRotatef_double

fun glRotatef_GLfloat : glRotate_type (GLfloat)
  = "atsctrb_glRotatef_GLfloat"
overload glRotatef with glRotatef_GLfloat

(* ****** ****** *)

typedef glScale_type (a:t@ype) =
  (a(*x*), a(*y*), a(*z*)) -<fun1> void

symintr glScaled

fun glScaled_double : glScale_type (double)
  = "atsctrb_glScaled_double"
overload glScaled with glScaled_double

fun glScaled_GLdouble : glScale_type (GLdouble)
  = "atsctrb_glScaled_GLdouble"
overload glScaled with glScaled_GLdouble

symintr glScalef

fun glScalef_double : glScale_type (double)
  = "atsctrb_glScalef_double"
overload glScalef with glScalef_double

fun glScalef_GLfloat : glScale_type (GLfloat)
  = "atsctrb_glScalef_GLfloat"
overload glScalef with glScalef_GLfloat

(* ****** ****** *)

typedef glTranslate_type (a:t@ype) =
  (a(*x*), a(*y*), a(*z*)) -<fun1> void

symintr glTranslated

fun glTranslated_double : glTranslate_type (double)
  = "atsctrb_glTranslated_double"
overload glTranslated with glTranslated_double 

fun glTranslated_GLdouble : glTranslate_type (GLdouble)
  = "atsctrb_glTranslated_GLdouble"
overload glTranslated with glTranslated_GLdouble 

symintr glTranslatef

fun glTranslatef_double : glTranslate_type (double)
  = "atsctrb_glTranslatef_double"
overload glTranslatef with glTranslatef_double

fun glTranslatef_GLfloat : glTranslate_type (GLfloat)
  = "atsctrb_glTranslatef_GLfloat"
overload glTranslatef with glTranslatef_GLfloat

(* ****** ****** *)

// Display Lists

absview GLlist_v (int)
absview GLnewlist_v (int)

fun glIsList (lst: GLuint): GLboolean = "atsctrb_glIsList"

fun glDeleteList {n:nat} (pf: GLlist_v n | lst: uint n): void
  = "ats_glDeleteList"

// fun glDeleteLists (lst: GLuint, range: GLsizei): void = "atsctrb_glDeleteLists"

fun glGenList_exn (): [n:nat] @(GLnewlist_v n | uint n) = "atsctrb_glGenList_exn"

// fun glGenLists (range: GLsizei): GLuint = "atsctrb_glGenLists"

absview glNewListView

fun glNewList {n:nat}
  (pf: !GLnewlist_v n >> GLlist_v n | lst: uint n, mode: GLenum): @(glNewListView | void)
  = "atsctrb_glNewList"

fun glEndList (pf: glNewListView | (*none*)): void
  = "atsctrb_glEndList"

fun glCallList {n:nat}
  (pf: !GLlist_v n | lst: uint n): void = "atsctrb_glCallList"

// fun glCallLists (n: GLsizei, typ: GLenum, lst: GLvoid* ): void

// fun glListBase (base: GLuint): void

(* ****** ****** *)

/*
** Drawing Functions
*/

absview glBeginView
fun glBegin (mode: GLenum): @(glBeginView | void) = "atsctrb_glBegin"
fun glEnd (pf: glBeginView | (*none*)): void = "atsctrb_glEnd"

(* ****** ****** *)

typedef glVertex2_type (a:t@ype) = (a(*x*), a(*y*)) -<fun1> void

symintr glVertex2d

fun glVertex2d_double : glVertex2_type (double)
  = "atsctrb_glVertex2d_double"
overload glVertex2d with glVertex2d_double

fun glVertex2d_GLdouble : glVertex2_type (GLdouble)
  = "atsctrb_glVertex2d_GLdouble"
overload glVertex2d with glVertex2d_GLdouble

//

symintr glVertex2f
fun glVertex2f_double : glVertex2_type (double)
  = "atsctrb_glVertex2f_double"
overload glVertex2f with glVertex2f_double

fun glVertex2f_GLfloat : glVertex2_type (GLfloat)
  = "atsctrb_glVertex2f_GLfloat"
overload glVertex2f with glVertex2f_GLfloat

//

fun glVertex2i (x: GLint, y: GLint): void = "atsctrb_glVertex2i"
fun glVertex2s (x: GLshort, y: GLshort): void = "atsctrb_glVertex2s"

(* ****** ****** *)

typedef glVertex3_type (a:t@ype) =
  (a(*x*), a(*y*), a(*z*)) -<fun1> void

//

fun glVertex3d : glVertex3_type (GLdouble)
  = "atsctrb_glVertex3d"

//

symintr glVertex3f

fun glVertex3f_double : glVertex3_type (double)
  = "atsctrb_glVertex3f_double"
overload glVertex3f with glVertex3f_double

fun glVertex3f_GLfloat : glVertex3_type (GLfloat)
  = "atsctrb_glVertex3f_GLfloat"
overload glVertex3f with glVertex3f_GLfloat

//

fun glVertex3i : glVertex3_type (GLint)
  = "atsctrb_glVertex3i"

fun glVertex3s : glVertex3_type (GLshort)
  = "atsctrb_glVertex3s"

(* ****** ****** *)

typedef glVertex4_type (a:t@ype) =
  (a(*x*), a(*y*), a(*z*), a(*w*)) -<fun1> void

fun glVertex4d : glVertex4_type (GLdouble)
  = "atsctrb_glVertex4d"

fun glVertex4f : glVertex4_type (GLfloat)
  = "atsctrb_glVertex4f"

fun glVertex4i : glVertex4_type (GLint)
  = "atsctrb_glVertex4i"

fun glVertex4s : glVertex4_type (GLshort)
  = "atsctrb_glVertex4s"

//

fun glVertex2dv {l:addr}
  (pf: !array_v (GLdouble, 2, l) | p: ptr l): void
  = "atsctrb_glVertex2dv"

fun glVertex2fv {l:addr}
  (pf: !array_v (GLfloat, 2, l) | p: ptr l): void
  = "atsctrb_glVertex2fv"

fun glVertex2iv {l:addr}
  (pf: !array_v (GLint, 2, l) | p: ptr l): void
  = "atsctrb_glVertex2iv"

fun glVertex2sv {l:addr}
  (pf: !array_v (GLshort, 2, l) | p: ptr l): void
  = "atsctrb_glVertex2sv"

//

fun glVertex3dv {l:addr}
  (pf: !array_v (GLdouble, 3, l) | p: ptr l): void
  = "atsctrb_glVertex3dv"

fun glVertex3fv {l:addr}
  (pf: !array_v (GLfloat, 3, l) | p: ptr l): void
  = "atsctrb_glVertex3fv"

fun glVertex3iv {l:addr}
  (pf: !array_v (GLint, 3, l) | p: ptr l): void
  = "atsctrb_glVertex3iv"

fun glVertex3sv {l:addr}
  (pf: !array_v (GLshort, 3, l) | p: ptr l): void
  = "atsctrb_glVertex3sv"

//

fun glVertex4dv {l:addr}
  (pf: !array_v (GLdouble, 4, l) | p: ptr l): void
  = "atsctrb_glVertex4dv"

fun glVertex4fv {l:addr}
  (pf: !array_v (GLfloat, 4, l) | p: ptr l): void
  = "atsctrb_glVertex4fv"

fun glVertex4iv {l:addr}
  (pf: !array_v (GLint, 4, l) | p: ptr l): void
  = "atsctrb_glVertex4iv"

fun glVertex4sv {l:addr}
  (pf: !array_v (GLshort, 4, l) | p: ptr l): void
  = "atsctrb_glVertex4sv"

(* ****** ****** *)

fun glNormal3b (nx: GLbyte, ny: GLbyte, nz: GLbyte): void = "atsctrb_glNormal3b"
fun glNormal3d (nx: GLdouble, ny: GLdouble, nz: GLdouble): void = "atsctrb_glNormal3d"
fun glNormal3f (nx: GLfloat, ny: GLfloat, nz: GLfloat): void = "atsctrb_glNormal3f"
fun glNormal3i (nx: GLint, ny: GLint, nz: GLint): void = "atsctrb_glNormal3i"
fun glNormal3s (nx: GLshort, ny: GLshort, nz: GLshort): void = "atsctrb_glNormal3s"

fun glNormal3bv {l:addr}
  (pf: array_v (GLbyte, 3, l) | ptr: ptr l): void
  = "atsctrb_glNormal3bv"

fun glNormal3dv {l:addr}
  (pf: array_v (GLdouble, 3, l) | ptr: ptr l): void
  = "atsctrb_glNormal3dv"

fun glNormal3fv {l:addr}
  (pf: array_v (GLfloat, 3, l) | ptr: ptr l): void
  = "atsctrb_glNormal3fv"

fun glNormal3iv {l:addr}
  (pf: array_v (GLint, 3, l) | ptr: ptr l): void
  = "atsctrb_glNormal3iv"

fun glNormal3sv {l:addr}
  (pf: array_v (GLshort, 3, l) | ptr: ptr l): void
  = "atsctrb_glNormal3sv"

(* ****** ****** *)

fun glIndexd (c: GLdouble): void = "atsctrb_glIndexd"
fun glIndexf (c: GLfloat): void = "atsctrb_glIndexf"
fun glIndexi (c: GLint): void = "atsctrb_glIndexi"
fun glIndexs (c: GLshort): void = "atsctrb_glIndexs"
fun glIndexub (c: GLubyte): void = "atsctrb_glIndexub" // OpenGL 1.1

(*
GLAPI void GLAPIENTRY glIndexdv( const GLdouble *c );
GLAPI void GLAPIENTRY glIndexfv( const GLfloat *c );
GLAPI void GLAPIENTRY glIndexiv( const GLint *c );
GLAPI void GLAPIENTRY glIndexsv( const GLshort *c );
GLAPI void GLAPIENTRY glIndexubv( const GLubyte *c );  /* 1.1 */
*)

//

typedef glColor3_type (a:t@ype) =
  (a(*red*), a(*green*), a(*blue*)) -<fun1> void

//

fun glColor3b : glColor3_type (GLbyte) = "atsctrb_glColor3b"
fun glColor3d : glColor3_type (GLdouble) = "atsctrb_glColor3d"

//

symintr glColor3f

fun glColor3f_double : glColor3_type (double)
  = "atsctrb_glColor3f_double"
overload glColor3f with glColor3f_double

fun glColor3f_GLfloat : glColor3_type (GLfloat)
  = "atsctrb_glColor3f_GLfloat"
overload glColor3f with glColor3f_GLfloat

//

fun glColor3i : glColor3_type (GLint)
  = "atsctrb_glColor3i"

fun glColor3s : glColor3_type (GLshort)
  = "atsctrb_glColor3s"

fun glColor3ub : glColor3_type (GLubyte)
  = "atsctrb_glColor3ub"

fun glColor3ui : glColor3_type (GLuint)
  = "atsctrb_glColor3ui"

fun glColor3us : glColor3_type (GLushort)
  = "atsctrb_glColor3us"

(* ****** ****** *)

typedef glColor4_type (a:t@ype) =
  (a(*red*), a(*green*), a(*blue*), a(*alpha*)) -<fun1> void

fun glColor4b : glColor4_type (GLbyte)
  = "atsctrb_glColor4b"

fun glColor4d : glColor4_type (GLdouble)
  = "atsctrb_glColor4d"

//

symintr glColor4f

fun glColor4f_double : glColor4_type (double)
  = "atsctrb_glColor4f_double"
overload glColor4f with glColor4f_double

fun glColor4f_GLfloat : glColor4_type (GLfloat)
  = "atsctrb_glColor4f_GLfloat"
overload glColor4f with glColor4f_GLfloat

//

fun glColor4i : glColor4_type (GLint)
  = "atsctrb_glColor4i"

fun glColor4s : glColor4_type (GLshort)
  = "atsctrb_glColor4s"

fun glColor4ub : glColor4_type (GLubyte)
  = "atsctrb_glColor4ub"

fun glColor4ui : glColor4_type (GLuint)
  = "atsctrb_glColor4ui"

fun glColor4us : glColor4_type (GLushort)
  = "atsctrb_glColor4us"

(* ****** ****** *)

(*

GLAPI void GLAPIENTRY glColor3bv( const GLbyte *v );
GLAPI void GLAPIENTRY glColor3dv( const GLdouble *v );
GLAPI void GLAPIENTRY glColor3fv( const GLfloat *v );
GLAPI void GLAPIENTRY glColor3iv( const GLint *v );
GLAPI void GLAPIENTRY glColor3sv( const GLshort *v );
GLAPI void GLAPIENTRY glColor3ubv( const GLubyte *v );
GLAPI void GLAPIENTRY glColor3uiv( const GLuint *v );
GLAPI void GLAPIENTRY glColor3usv( const GLushort *v );

GLAPI void GLAPIENTRY glColor4bv( const GLbyte *v );
GLAPI void GLAPIENTRY glColor4dv( const GLdouble *v );
GLAPI void GLAPIENTRY glColor4fv( const GLfloat *v );
GLAPI void GLAPIENTRY glColor4iv( const GLint *v );
GLAPI void GLAPIENTRY glColor4sv( const GLshort *v );
GLAPI void GLAPIENTRY glColor4ubv( const GLubyte *v );
GLAPI void GLAPIENTRY glColor4uiv( const GLuint *v );
GLAPI void GLAPIENTRY glColor4usv( const GLushort *v );

*)

fun glTexCoord1d (s: GLdouble): void = "atsctrb_glTexCoord1d"
fun glTexCoord1f (s: GLfloat): void = "atsctrb_glTexCoord1f"
fun glTexCoord1i (s: GLint): void = "atsctrb_glTexCoord1i"
fun glTexCoord1s (s: GLshort): void = "atsctrb_glTexCoord1s"

fun glTexCoord2d (s: GLdouble, t: GLdouble): void = "atsctrb_glTexCoord2d"
fun glTexCoord2f (s: GLfloat, t: GLfloat): void = "atsctrb_glTexCoord2f"
fun glTexCoord2i (s: GLint, t: GLint): void = "atsctrb_glTexCoord2i"
fun glTexCoord2s (s: GLshort, t: GLshort): void = "atsctrb_glTexCoord2s"

fun glTexCoord3d (s: GLdouble, t: GLdouble, r: GLdouble): void = "atsctrb_glTexCoord3d"
fun glTexCoord3f (s: GLfloat, t: GLfloat, r: GLfloat): void = "atsctrb_glTexCoord3f"
fun glTexCoord3i (s: GLint, t: GLint, r: GLint): void = "atsctrb_glTexCoord3i"
fun glTexCoord3s (s: GLshort, t: GLshort, r: GLshort): void = "atsctrb_glTexCoord3s"

fun glTexCoord4d (s: GLdouble, t: GLdouble, r: GLdouble, q: GLdouble): void = "atsctrb_glTexCoord4d"
fun glTexCoord4f (s: GLfloat, t: GLfloat, r: GLfloat, q: GLfloat): void = "atsctrb_glTexCoord4f"
fun glTexCoord4i (s: GLint, t: GLint, r: GLint, q: GLint): void = "atsctrb_glTexCoord4i"
fun glTexCoord4s (s: GLshort, t: GLshort, r: GLshort, q: GLshort): void = "atsctrb_glTexCoord4s"

(*

GLAPI void GLAPIENTRY glTexCoord1dv( const GLdouble *v );
GLAPI void GLAPIENTRY glTexCoord1fv( const GLfloat *v );
GLAPI void GLAPIENTRY glTexCoord1iv( const GLint *v );
GLAPI void GLAPIENTRY glTexCoord1sv( const GLshort *v );

GLAPI void GLAPIENTRY glTexCoord2dv( const GLdouble *v );
GLAPI void GLAPIENTRY glTexCoord2fv( const GLfloat *v );
GLAPI void GLAPIENTRY glTexCoord2iv( const GLint *v );
GLAPI void GLAPIENTRY glTexCoord2sv( const GLshort *v );

GLAPI void GLAPIENTRY glTexCoord3dv( const GLdouble *v );
GLAPI void GLAPIENTRY glTexCoord3fv( const GLfloat *v );
GLAPI void GLAPIENTRY glTexCoord3iv( const GLint *v );
GLAPI void GLAPIENTRY glTexCoord3sv( const GLshort *v );

GLAPI void GLAPIENTRY glTexCoord4dv( const GLdouble *v );
GLAPI void GLAPIENTRY glTexCoord4fv( const GLfloat *v );
GLAPI void GLAPIENTRY glTexCoord4iv( const GLint *v );
GLAPI void GLAPIENTRY glTexCoord4sv( const GLshort *v );

*)

(* ****** ****** *)

typedef glRasterPos2_type
  (a:t@ype) = (a(*x*), a(*y*)) -<fun1> void
// end of [glRasterPos2_type]

//

symintr glRasterPos2d

fun glRasterPos2d_double : glRasterPos2_type (double)
  = "atsctrb_glRasterPos2d_double"
overload glRasterPos2d with glRasterPos2d_double

fun glRasterPos2d_GLdouble : glRasterPos2_type (GLdouble)
  = "atsctrb_glRasterPos2d_GLdouble"
overload glRasterPos2d with glRasterPos2d_GLdouble

//

symintr glRasterPos2f

fun glRasterPos2f_double : glRasterPos2_type (double)
  = "atsctrb_glRasterPos2f_double"
overload glRasterPos2f with glRasterPos2f_double

fun glRasterPos2f_GLfloat : glRasterPos2_type (GLfloat)
  = "atsctrb_glRasterPos2f_GLfloat"
overload glRasterPos2f with glRasterPos2f_GLfloat

//

fun glRasterPos2i : glRasterPos2_type (GLint) = "atsctrb_glRasterPos2i"
fun glRasterPos2s : glRasterPos2_type (GLshort) = "atsctrb_glRasterPos2s"

(* ****** ****** *)

typedef glRasterPos3_type
  (a:t@ype) = (a(*x*), a(*y*), a(*z*)) -<fun1> void
// end of [glRasterPos3_type]

fun glRasterPos3d : glRasterPos3_type (GLdouble) = "atsctrb_glRasterPos3d"
fun glRasterPos3f : glRasterPos3_type (GLfloat)  = "atsctrb_glRasterPos3f"
fun glRasterPos3i : glRasterPos3_type (GLint) = "atsctrb_glRasterPos3i"
fun glRasterPos3s : glRasterPos3_type (GLshort) = "atsctrb_glRasterPos3s"

(* ****** ****** *)

typedef glRasterPos4_type
  (a:t@ype) = (a(*x*), a(*y*), a(*z*), a(*w*)) -<fun1> void
// end of [glRasterPos4_type]

fun glRasterPos4d : glRasterPos4_type (GLdouble) = "atsctrb_glRasterPos4d"
fun glRasterPos4f : glRasterPos4_type (GLfloat)  = "atsctrb_glRasterPos4f"
fun glRasterPos4i : glRasterPos4_type (GLint) = "atsctrb_glRasterPos4i"
fun glRasterPos4s : glRasterPos4_type (GLshort) = "atsctrb_glRasterPos4s"

(*

GLAPI void GLAPIENTRY glRasterPos2dv( const GLdouble *v );
GLAPI void GLAPIENTRY glRasterPos2fv( const GLfloat *v );
GLAPI void GLAPIENTRY glRasterPos2iv( const GLint *v );
GLAPI void GLAPIENTRY glRasterPos2sv( const GLshort *v );

GLAPI void GLAPIENTRY glRasterPos3dv( const GLdouble *v );
GLAPI void GLAPIENTRY glRasterPos3fv( const GLfloat *v );
GLAPI void GLAPIENTRY glRasterPos3iv( const GLint *v );
GLAPI void GLAPIENTRY glRasterPos3sv( const GLshort *v );

GLAPI void GLAPIENTRY glRasterPos4dv( const GLdouble *v );
GLAPI void GLAPIENTRY glRasterPos4fv( const GLfloat *v );
GLAPI void GLAPIENTRY glRasterPos4iv( const GLint *v );
GLAPI void GLAPIENTRY glRasterPos4sv( const GLshort *v );

*)

(* ****** ****** *)

typedef glRect_type (a:t@ype) =
 (a(*x1*), a(*y1*), a(*x2*), a(*y2*)) -<fun1> void

//

symintr glRectd

fun glRectd_double : glRect_type (double)
  = "atsctrb_glRectd_double"
overload glRectd with glRectd_double

fun glRectd_GLdouble : glRect_type (GLdouble)
  = "atsctrb_glRectd_GLdouble"
overload glRectd with glRectd_GLdouble

//

symintr glRectf

fun glRectf_double : glRect_type (double)
  = "atsctrb_glRectf_double"
overload glRectf with glRectf_double

fun glRectf_GLfloat : glRect_type (GLfloat)
  = "atsctrb_glRectf_GLfloat"
overload glRectf with glRectf_GLfloat

//

fun glRecti : glRect_type (GLint)
  = "atsctrb_glRecti"

fun glRects : glRect_type (GLshort)
  = "atsctrb_glRects"

(*

GLAPI void GLAPIENTRY glRectdv( const GLdouble *v1, const GLdouble *v2 );
GLAPI void GLAPIENTRY glRectfv( const GLfloat *v1, const GLfloat *v2 );
GLAPI void GLAPIENTRY glRectiv( const GLint *v1, const GLint *v2 );
GLAPI void GLAPIENTRY glRectsv( const GLshort *v1, const GLshort *v2 );

*)

(* ****** ****** *)


// Lighting

fun glShadeModel (mode: GLenum): void = "atsctrb_glShadeModel"

fun glLightf (light: GLenum, pname: GLenum, param: GLfloat): void
  = "atsctrb_glLightf"

fun glLighti (light: GLenum, pname: GLenum, param: GLint): void
  = "atsctrb_glLighti"

// these are really unsafe functions!
fun glLightfv {n:nat} {l:addr}
  (pf: !array_v (GLfloat, n, l) | light: GLenum, pname: GLenum, p: ptr l): void
  = "atsctrb_glLightfv"

fun glLightiv {n:nat} {l:addr}
  (pf: !array_v (GLint, n, l) | light: GLenum, pname: GLenum, p: ptr l): void
  = "atsctrb_glLightiv"

(*
GLAPI void GLAPIENTRY glGetLightfv( GLenum light, GLenum pname,
                                    GLfloat *params );
GLAPI void GLAPIENTRY glGetLightiv( GLenum light, GLenum pname,
                                    GLint *params );
*)

fun glLightModelf(pname: GLenum, param: GLfloat): void
  = "atsctrb_glLightModelf"

fun glLightModeli(pname: GLenum, param: GLint): void
  = "atsctrb_glLightModeli"

fun glLightModelfv {n:nat} {l:addr}
  (pf: !array_v (GLfloat, n, l) | pname: GLenum, params: ptr l): void
  = "atsctrb_glLightModelfv"

fun glLightModeliv {n:nat} {l:addr}
  (pf: !array_v (GLint, n, l) | pname: GLenum, params: ptr l): void
  = "atsctrb_glLightModeliv"

(* ****** ****** *)

fun glMaterialf (face: GLenum, pname: GLenum, param: GLfloat): void
  = "atsctrb_glMaterialf"

fun glMateriali (face: GLenum, pname: GLenum, param: GLint): void
  = "atsctrb_glMateriali"

fun glMaterialfv {n:nat} {l:addr}
  (pf: !array_v (GLfloat, n, l) | face: GLenum, pname: GLenum, params: ptr l): void
  = "atsctrb_glMaterialfv"

fun glMaterialiv {n:nat} {l:addr}
  (pf: !array_v (GLint, n, l) | face: GLenum, pname: GLenum, params: ptr l): void
  = "atsctrb_glMaterialiv"

fun glGetMaterialfv {n:nat} {l:addr}
  (pf: !array_v (GLfloat?, n, l) | face: GLenum, pname: GLenum, params: ptr l): void
  = "atsctrb_glGetMaterialfv"

fun glGetMaterialiv {n:nat} {l:addr}
  (pf: !array_v (GLint?, n, l) | face: GLenum, pname: GLenum, params: ptr l): void
  = "atsctrb_glGetMaterialiv"

(* ****** ****** *)

fun glColorMaterial (face: GLenum, mode: GLenum): void = "atsctrb_glColorMaterial"

(* ****** ****** *)

// OpenGL 1.2

(* ****** ****** *)

macdef GL_RESCALE_NORMAL = $extval (GLenum, "GL_RESCALE_NORMAL")
macdef GL_CLAMP_TO_EDGE = $extval (GLenum, "GL_CLAMP_TO_EDGE")
macdef GL_MAX_ELEMENTS_VERTICES = $extval (GLenum, "GL_MAX_ELEMENTS_VERTICES")
macdef GL_MAX_ELEMENTS_INDICES = $extval (GLenum, "GL_MAX_ELEMENTS_INDICES")
macdef GL_BGR = $extval (GLenum, "GL_BGR")
macdef GL_BGRA = $extval (GLenum, "GL_BGRA")
macdef GL_UNSIGNED_BYTE_3_3_2 = $extval (GLenum, "GL_UNSIGNED_BYTE_3_3_2")
macdef GL_UNSIGNED_BYTE_2_3_3_REV = $extval (GLenum, "GL_UNSIGNED_BYTE_2_3_3_REV")
macdef GL_UNSIGNED_SHORT_5_6_5 = $extval (GLenum, "GL_UNSIGNED_SHORT_5_6_5")
macdef GL_UNSIGNED_SHORT_5_6_5_REV = $extval (GLenum, "GL_UNSIGNED_SHORT_5_6_5_REV")
macdef GL_UNSIGNED_SHORT_4_4_4_4 = $extval (GLenum, "GL_UNSIGNED_SHORT_4_4_4_4")
macdef GL_UNSIGNED_SHORT_4_4_4_4_REV = $extval (GLenum, "GL_UNSIGNED_SHORT_4_4_4_4_REV")
macdef GL_UNSIGNED_SHORT_5_5_5_1 = $extval (GLenum, "GL_UNSIGNED_SHORT_5_5_5_1")
macdef GL_UNSIGNED_SHORT_1_5_5_5_REV = $extval (GLenum, "GL_UNSIGNED_SHORT_1_5_5_5_REV")
macdef GL_UNSIGNED_INT_8_8_8_8 = $extval (GLenum, "GL_UNSIGNED_INT_8_8_8_8")
macdef GL_UNSIGNED_INT_8_8_8_8_REV = $extval (GLenum, "GL_UNSIGNED_INT_8_8_8_8_REV")
macdef GL_UNSIGNED_INT_10_10_10_2 = $extval (GLenum, "GL_UNSIGNED_INT_10_10_10_2")
macdef GL_UNSIGNED_INT_2_10_10_10_REV = $extval (GLenum, "GL_UNSIGNED_INT_2_10_10_10_REV")
macdef GL_LIGHT_MODEL_COLOR_CONTROL = $extval (GLenum, "GL_LIGHT_MODEL_COLOR_CONTROL")
macdef GL_SINGLE_COLOR = $extval (GLenum, "GL_SINGLE_COLOR")
macdef GL_SEPARATE_SPECULAR_COLOR = $extval (GLenum, "GL_SEPARATE_SPECULAR_COLOR")
macdef GL_TEXTURE_MIN_LOD = $extval (GLenum, "GL_TEXTURE_MIN_LOD")
macdef GL_TEXTURE_MAX_LOD = $extval (GLenum, "GL_TEXTURE_MAX_LOD")
macdef GL_TEXTURE_BASE_LEVEL = $extval (GLenum, "GL_TEXTURE_BASE_LEVEL")
macdef GL_TEXTURE_MAX_LEVEL = $extval (GLenum, "GL_TEXTURE_MAX_LEVEL")
macdef GL_SMOOTH_POINT_SIZE_RANGE = $extval (GLenum, "GL_SMOOTH_POINT_SIZE_RANGE")
macdef GL_SMOOTH_POINT_SIZE_GRANULARITY = $extval (GLenum, "GL_SMOOTH_POINT_SIZE_GRANULARITY")
macdef GL_SMOOTH_LINE_WIDTH_RANGE = $extval (GLenum, "GL_SMOOTH_LINE_WIDTH_RANGE")
macdef GL_SMOOTH_LINE_WIDTH_GRANULARITY = $extval (GLenum, "GL_SMOOTH_LINE_WIDTH_GRANULARITY")
macdef GL_ALIASED_POINT_SIZE_RANGE = $extval (GLenum, "GL_ALIASED_POINT_SIZE_RANGE")
macdef GL_ALIASED_LINE_WIDTH_RANGE = $extval (GLenum, "GL_ALIASED_LINE_WIDTH_RANGE")
macdef GL_PACK_SKIP_IMAGES = $extval (GLenum, "GL_PACK_SKIP_IMAGES")
macdef GL_PACK_IMAGE_HEIGHT = $extval (GLenum, "GL_PACK_IMAGE_HEIGHT")
macdef GL_UNPACK_SKIP_IMAGES = $extval (GLenum, "GL_UNPACK_SKIP_IMAGES")
macdef GL_UNPACK_IMAGE_HEIGHT = $extval (GLenum, "GL_UNPACK_IMAGE_HEIGHT")
macdef GL_TEXTURE_3D = $extval (GLenum, "GL_TEXTURE_3D")
macdef GL_PROXY_TEXTURE_3D = $extval (GLenum, "GL_PROXY_TEXTURE_3D")
macdef GL_TEXTURE_DEPTH = $extval (GLenum, "GL_TEXTURE_DEPTH")
macdef GL_TEXTURE_WRAP_R = $extval (GLenum, "GL_TEXTURE_WRAP_R")
macdef GL_MAX_3D_TEXTURE_SIZE = $extval (GLenum, "GL_MAX_3D_TEXTURE_SIZE")
macdef GL_TEXTURE_BINDING_3D = $extval (GLenum, "GL_TEXTURE_BINDING_3D")

(* ****** ****** *)

// GL_ARB_imaging

(* ****** ****** *)

macdef GL_CONSTANT_COLOR = $extval (GLenum, "GL_CONSTANT_COLOR")
macdef GL_ONE_MINUS_CONSTANT_COLOR = $extval (GLenum, "GL_ONE_MINUS_CONSTANT_COLOR")
macdef GL_CONSTANT_ALPHA = $extval (GLenum, "GL_CONSTANT_ALPHA")
macdef GL_ONE_MINUS_CONSTANT_ALPHA = $extval (GLenum, "GL_ONE_MINUS_CONSTANT_ALPHA")
macdef GL_COLOR_TABLE = $extval (GLenum, "GL_COLOR_TABLE")
macdef GL_POST_CONVOLUTION_COLOR_TABLE = $extval (GLenum, "GL_POST_CONVOLUTION_COLOR_TABLE")
macdef GL_POST_COLOR_MATRIX_COLOR_TABLE = $extval (GLenum, "GL_POST_COLOR_MATRIX_COLOR_TABLE")
macdef GL_PROXY_COLOR_TABLE = $extval (GLenum, "GL_PROXY_COLOR_TABLE")
macdef GL_PROXY_POST_CONVOLUTION_COLOR_TABLE = $extval (GLenum, "GL_PROXY_POST_CONVOLUTION_COLOR_TABLE")
macdef GL_PROXY_POST_COLOR_MATRIX_COLOR_TABLE = $extval (GLenum, "GL_PROXY_POST_COLOR_MATRIX_COLOR_TABLE")
macdef GL_COLOR_TABLE_SCALE = $extval (GLenum, "GL_COLOR_TABLE_SCALE")
macdef GL_COLOR_TABLE_BIAS = $extval (GLenum, "GL_COLOR_TABLE_BIAS")
macdef GL_COLOR_TABLE_FORMAT = $extval (GLenum, "GL_COLOR_TABLE_FORMAT")
macdef GL_COLOR_TABLE_WIDTH = $extval (GLenum, "GL_COLOR_TABLE_WIDTH")
macdef GL_COLOR_TABLE_RED_SIZE = $extval (GLenum, "GL_COLOR_TABLE_RED_SIZE")
macdef GL_COLOR_TABLE_GREEN_SIZE = $extval (GLenum, "GL_COLOR_TABLE_GREEN_SIZE")
macdef GL_COLOR_TABLE_BLUE_SIZE = $extval (GLenum, "GL_COLOR_TABLE_BLUE_SIZE")
macdef GL_COLOR_TABLE_ALPHA_SIZE = $extval (GLenum, "GL_COLOR_TABLE_ALPHA_SIZE")
macdef GL_COLOR_TABLE_LUMINANCE_SIZE = $extval (GLenum, "GL_COLOR_TABLE_LUMINANCE_SIZE")
macdef GL_COLOR_TABLE_INTENSITY_SIZE = $extval (GLenum, "GL_COLOR_TABLE_INTENSITY_SIZE")
macdef GL_CONVOLUTION_1D = $extval (GLenum, "GL_CONVOLUTION_1D")
macdef GL_CONVOLUTION_2D = $extval (GLenum, "GL_CONVOLUTION_2D")
macdef GL_SEPARABLE_2D = $extval (GLenum, "GL_SEPARABLE_2D")
macdef GL_CONVOLUTION_BORDER_MODE = $extval (GLenum, "GL_CONVOLUTION_BORDER_MODE")
macdef GL_CONVOLUTION_FILTER_SCALE = $extval (GLenum, "GL_CONVOLUTION_FILTER_SCALE")
macdef GL_CONVOLUTION_FILTER_BIAS = $extval (GLenum, "GL_CONVOLUTION_FILTER_BIAS")
macdef GL_REDUCE = $extval (GLenum, "GL_REDUCE")
macdef GL_CONVOLUTION_FORMAT = $extval (GLenum, "GL_CONVOLUTION_FORMAT")
macdef GL_CONVOLUTION_WIDTH = $extval (GLenum, "GL_CONVOLUTION_WIDTH")
macdef GL_CONVOLUTION_HEIGHT = $extval (GLenum, "GL_CONVOLUTION_HEIGHT")
macdef GL_MAX_CONVOLUTION_WIDTH = $extval (GLenum, "GL_MAX_CONVOLUTION_WIDTH")
macdef GL_MAX_CONVOLUTION_HEIGHT = $extval (GLenum, "GL_MAX_CONVOLUTION_HEIGHT")
macdef GL_POST_CONVOLUTION_RED_SCALE = $extval (GLenum, "GL_POST_CONVOLUTION_RED_SCALE")
macdef GL_POST_CONVOLUTION_GREEN_SCALE = $extval (GLenum, "GL_POST_CONVOLUTION_GREEN_SCALE")
macdef GL_POST_CONVOLUTION_BLUE_SCALE = $extval (GLenum, "GL_POST_CONVOLUTION_BLUE_SCALE")
macdef GL_POST_CONVOLUTION_ALPHA_SCALE = $extval (GLenum, "GL_POST_CONVOLUTION_ALPHA_SCALE")
macdef GL_POST_CONVOLUTION_RED_BIAS = $extval (GLenum, "GL_POST_CONVOLUTION_RED_BIAS")
macdef GL_POST_CONVOLUTION_GREEN_BIAS = $extval (GLenum, "GL_POST_CONVOLUTION_GREEN_BIAS")
macdef GL_POST_CONVOLUTION_BLUE_BIAS = $extval (GLenum, "GL_POST_CONVOLUTION_BLUE_BIAS")
macdef GL_POST_CONVOLUTION_ALPHA_BIAS = $extval (GLenum, "GL_POST_CONVOLUTION_ALPHA_BIAS")
macdef GL_CONSTANT_BORDER = $extval (GLenum, "GL_CONSTANT_BORDER")
macdef GL_REPLICATE_BORDER = $extval (GLenum, "GL_REPLICATE_BORDER")
macdef GL_CONVOLUTION_BORDER_COLOR = $extval (GLenum, "GL_CONVOLUTION_BORDER_COLOR")
macdef GL_COLOR_MATRIX = $extval (GLenum, "GL_COLOR_MATRIX")
macdef GL_COLOR_MATRIX_STACK_DEPTH = $extval (GLenum, "GL_COLOR_MATRIX_STACK_DEPTH")
macdef GL_MAX_COLOR_MATRIX_STACK_DEPTH = $extval (GLenum, "GL_MAX_COLOR_MATRIX_STACK_DEPTH")
macdef GL_POST_COLOR_MATRIX_RED_SCALE = $extval (GLenum, "GL_POST_COLOR_MATRIX_RED_SCALE")
macdef GL_POST_COLOR_MATRIX_GREEN_SCALE = $extval (GLenum, "GL_POST_COLOR_MATRIX_GREEN_SCALE")
macdef GL_POST_COLOR_MATRIX_BLUE_SCALE = $extval (GLenum, "GL_POST_COLOR_MATRIX_BLUE_SCALE")
macdef GL_POST_COLOR_MATRIX_ALPHA_SCALE = $extval (GLenum, "GL_POST_COLOR_MATRIX_ALPHA_SCALE")
macdef GL_POST_COLOR_MATRIX_RED_BIAS = $extval (GLenum, "GL_POST_COLOR_MATRIX_RED_BIAS")
macdef GL_POST_COLOR_MATRIX_GREEN_BIAS = $extval (GLenum, "GL_POST_COLOR_MATRIX_GREEN_BIAS")
macdef GL_POST_COLOR_MATRIX_BLUE_BIAS = $extval (GLenum, "GL_POST_COLOR_MATRIX_BLUE_BIAS")
macdef GL_POST_COLOR_MATRIX_ALPHA_BIAS = $extval (GLenum, "GL_POST_COLOR_MATRIX_ALPHA_BIAS")
macdef GL_HISTOGRAM = $extval (GLenum, "GL_HISTOGRAM")
macdef GL_PROXY_HISTOGRAM = $extval (GLenum, "GL_PROXY_HISTOGRAM")
macdef GL_HISTOGRAM_WIDTH = $extval (GLenum, "GL_HISTOGRAM_WIDTH")
macdef GL_HISTOGRAM_FORMAT = $extval (GLenum, "GL_HISTOGRAM_FORMAT")
macdef GL_HISTOGRAM_RED_SIZE = $extval (GLenum, "GL_HISTOGRAM_RED_SIZE")
macdef GL_HISTOGRAM_GREEN_SIZE = $extval (GLenum, "GL_HISTOGRAM_GREEN_SIZE")
macdef GL_HISTOGRAM_BLUE_SIZE = $extval (GLenum, "GL_HISTOGRAM_BLUE_SIZE")
macdef GL_HISTOGRAM_ALPHA_SIZE = $extval (GLenum, "GL_HISTOGRAM_ALPHA_SIZE")
macdef GL_HISTOGRAM_LUMINANCE_SIZE = $extval (GLenum, "GL_HISTOGRAM_LUMINANCE_SIZE")
macdef GL_HISTOGRAM_SINK = $extval (GLenum, "GL_HISTOGRAM_SINK")
macdef GL_MINMAX = $extval (GLenum, "GL_MINMAX")
macdef GL_MINMAX_FORMAT = $extval (GLenum, "GL_MINMAX_FORMAT")
macdef GL_MINMAX_SINK = $extval (GLenum, "GL_MINMAX_SINK")
macdef GL_TABLE_TOO_LARGE = $extval (GLenum, "GL_TABLE_TOO_LARGE")
macdef GL_BLEND_EQUATION = $extval (GLenum, "GL_BLEND_EQUATION")
macdef GL_MIN = $extval (GLenum, "GL_MIN")
macdef GL_MAX = $extval (GLenum, "GL_MAX")
macdef GL_FUNC_ADD = $extval (GLenum, "GL_FUNC_ADD")
macdef GL_FUNC_SUBTRACT = $extval (GLenum, "GL_FUNC_SUBTRACT")
macdef GL_FUNC_REVERSE_SUBTRACT = $extval (GLenum, "GL_FUNC_REVERSE_SUBTRACT")
macdef GL_BLEND_COLOR = $extval (GLenum, "GL_BLEND_COLOR")

(* ****** ****** *)

// OpenGL 1.3

(* ****** ****** *)

// multitexture
macdef GL_TEXTURE0 = $extval (GLenum, "GL_TEXTURE0")
macdef GL_TEXTURE1 = $extval (GLenum, "GL_TEXTURE1")
macdef GL_TEXTURE2 = $extval (GLenum, "GL_TEXTURE2")
macdef GL_TEXTURE3 = $extval (GLenum, "GL_TEXTURE3")
macdef GL_TEXTURE4 = $extval (GLenum, "GL_TEXTURE4")
macdef GL_TEXTURE5 = $extval (GLenum, "GL_TEXTURE5")
macdef GL_TEXTURE6 = $extval (GLenum, "GL_TEXTURE6")
macdef GL_TEXTURE7 = $extval (GLenum, "GL_TEXTURE7")
macdef GL_TEXTURE8 = $extval (GLenum, "GL_TEXTURE8")
macdef GL_TEXTURE9 = $extval (GLenum, "GL_TEXTURE9")
macdef GL_TEXTURE10 = $extval (GLenum, "GL_TEXTURE10")
macdef GL_TEXTURE11 = $extval (GLenum, "GL_TEXTURE11")
macdef GL_TEXTURE12 = $extval (GLenum, "GL_TEXTURE12")
macdef GL_TEXTURE13 = $extval (GLenum, "GL_TEXTURE13")
macdef GL_TEXTURE14 = $extval (GLenum, "GL_TEXTURE14")
macdef GL_TEXTURE15 = $extval (GLenum, "GL_TEXTURE15")
macdef GL_TEXTURE16 = $extval (GLenum, "GL_TEXTURE16")
macdef GL_TEXTURE17 = $extval (GLenum, "GL_TEXTURE17")
macdef GL_TEXTURE18 = $extval (GLenum, "GL_TEXTURE18")
macdef GL_TEXTURE19 = $extval (GLenum, "GL_TEXTURE19")
macdef GL_TEXTURE20 = $extval (GLenum, "GL_TEXTURE20")
macdef GL_TEXTURE21 = $extval (GLenum, "GL_TEXTURE21")
macdef GL_TEXTURE22 = $extval (GLenum, "GL_TEXTURE22")
macdef GL_TEXTURE23 = $extval (GLenum, "GL_TEXTURE23")
macdef GL_TEXTURE24 = $extval (GLenum, "GL_TEXTURE24")
macdef GL_TEXTURE25 = $extval (GLenum, "GL_TEXTURE25")
macdef GL_TEXTURE26 = $extval (GLenum, "GL_TEXTURE26")
macdef GL_TEXTURE27 = $extval (GLenum, "GL_TEXTURE27")
macdef GL_TEXTURE28 = $extval (GLenum, "GL_TEXTURE28")
macdef GL_TEXTURE29 = $extval (GLenum, "GL_TEXTURE29")
macdef GL_TEXTURE30 = $extval (GLenum, "GL_TEXTURE30")
macdef GL_TEXTURE31 = $extval (GLenum, "GL_TEXTURE31")
macdef GL_ACTIVE_TEXTURE = $extval (GLenum, "GL_ACTIVE_TEXTURE")
macdef GL_CLIENT_ACTIVE_TEXTURE = $extval (GLenum, "GL_CLIENT_ACTIVE_TEXTURE")
macdef GL_MAX_TEXTURE_UNITS = $extval (GLenum, "GL_MAX_TEXTURE_UNITS")

// texture_cube_map
macdef GL_NORMAL_MAP = $extval (GLenum, "GL_NORMAL_MAP")
macdef GL_REFLECTION_MAP = $extval (GLenum, "GL_REFLECTION_MAP")
macdef GL_TEXTURE_CUBE_MAP = $extval (GLenum, "GL_TEXTURE_CUBE_MAP")
macdef GL_TEXTURE_BINDING_CUBE_MAP = $extval (GLenum, "GL_TEXTURE_BINDING_CUBE_MAP")
macdef GL_TEXTURE_CUBE_MAP_POSITIVE_X = $extval (GLenum, "GL_TEXTURE_CUBE_MAP_POSITIVE_X")
macdef GL_TEXTURE_CUBE_MAP_NEGATIVE_X = $extval (GLenum, "GL_TEXTURE_CUBE_MAP_NEGATIVE_X")
macdef GL_TEXTURE_CUBE_MAP_POSITIVE_Y = $extval (GLenum, "GL_TEXTURE_CUBE_MAP_POSITIVE_Y")
macdef GL_TEXTURE_CUBE_MAP_NEGATIVE_Y = $extval (GLenum, "GL_TEXTURE_CUBE_MAP_NEGATIVE_Y")
macdef GL_TEXTURE_CUBE_MAP_POSITIVE_Z = $extval (GLenum, "GL_TEXTURE_CUBE_MAP_POSITIVE_Z")
macdef GL_TEXTURE_CUBE_MAP_NEGATIVE_Z = $extval (GLenum, "GL_TEXTURE_CUBE_MAP_NEGATIVE_Z")
macdef GL_PROXY_TEXTURE_CUBE_MAP = $extval (GLenum, "GL_PROXY_TEXTURE_CUBE_MAP")
macdef GL_MAX_CUBE_MAP_TEXTURE_SIZE = $extval (GLenum, "GL_MAX_CUBE_MAP_TEXTURE_SIZE")

// texture_compression
macdef GL_COMPRESSED_ALPHA = $extval (GLenum, "GL_COMPRESSED_ALPHA")
macdef GL_COMPRESSED_LUMINANCE = $extval (GLenum, "GL_COMPRESSED_LUMINANCE")
macdef GL_COMPRESSED_LUMINANCE_ALPHA = $extval (GLenum, "GL_COMPRESSED_LUMINANCE_ALPHA")
macdef GL_COMPRESSED_INTENSITY = $extval (GLenum, "GL_COMPRESSED_INTENSITY")
macdef GL_COMPRESSED_RGB = $extval (GLenum, "GL_COMPRESSED_RGB")
macdef GL_COMPRESSED_RGBA = $extval (GLenum, "GL_COMPRESSED_RGBA")
macdef GL_TEXTURE_COMPRESSION_HINT = $extval (GLenum, "GL_TEXTURE_COMPRESSION_HINT")
macdef GL_TEXTURE_COMPRESSED_IMAGE_SIZE = $extval (GLenum, "GL_TEXTURE_COMPRESSED_IMAGE_SIZE")
macdef GL_TEXTURE_COMPRESSED = $extval (GLenum, "GL_TEXTURE_COMPRESSED")
macdef GL_NUM_COMPRESSED_TEXTURE_FORMATS = $extval (GLenum, "GL_NUM_COMPRESSED_TEXTURE_FORMATS")
macdef GL_COMPRESSED_TEXTURE_FORMATS = $extval (GLenum, "GL_COMPRESSED_TEXTURE_FORMATS")

// multisample
macdef GL_MULTISAMPLE = $extval (GLenum, "GL_MULTISAMPLE")
macdef GL_SAMPLE_ALPHA_TO_COVERAGE = $extval (GLenum, "GL_SAMPLE_ALPHA_TO_COVERAGE")
macdef GL_SAMPLE_ALPHA_TO_ONE = $extval (GLenum, "GL_SAMPLE_ALPHA_TO_ONE")
macdef GL_SAMPLE_COVERAGE = $extval (GLenum, "GL_SAMPLE_COVERAGE")
macdef GL_SAMPLE_BUFFERS = $extval (GLenum, "GL_SAMPLE_BUFFERS")
macdef GL_SAMPLES = $extval (GLenum, "GL_SAMPLES")
macdef GL_SAMPLE_COVERAGE_VALUE = $extval (GLenum, "GL_SAMPLE_COVERAGE_VALUE")
macdef GL_SAMPLE_COVERAGE_INVERT = $extval (GLenum, "GL_SAMPLE_COVERAGE_INVERT")
macdef GL_MULTISAMPLE_BIT = $extval (GLenum, "GL_MULTISAMPLE_BIT")

// transpose_matrix
macdef GL_TRANSPOSE_MODELVIEW_MATRIX = $extval (GLenum, "GL_TRANSPOSE_MODELVIEW_MATRIX")
macdef GL_TRANSPOSE_PROJECTION_MATRIX = $extval (GLenum, "GL_TRANSPOSE_PROJECTION_MATRIX")
macdef GL_TRANSPOSE_TEXTURE_MATRIX = $extval (GLenum, "GL_TRANSPOSE_TEXTURE_MATRIX")
macdef GL_TRANSPOSE_COLOR_MATRIX = $extval (GLenum, "GL_TRANSPOSE_COLOR_MATRIX")

// texture_env_combine
macdef GL_COMBINE = $extval (GLenum, "GL_COMBINE")
macdef GL_COMBINE_RGB = $extval (GLenum, "GL_COMBINE_RGB")
macdef GL_COMBINE_ALPHA = $extval (GLenum, "GL_COMBINE_ALPHA")
macdef GL_SOURCE0_RGB = $extval (GLenum, "GL_SOURCE0_RGB")
macdef GL_SOURCE1_RGB = $extval (GLenum, "GL_SOURCE1_RGB")
macdef GL_SOURCE2_RGB = $extval (GLenum, "GL_SOURCE2_RGB")
macdef GL_SOURCE0_ALPHA = $extval (GLenum, "GL_SOURCE0_ALPHA")
macdef GL_SOURCE1_ALPHA = $extval (GLenum, "GL_SOURCE1_ALPHA")
macdef GL_SOURCE2_ALPHA = $extval (GLenum, "GL_SOURCE2_ALPHA")
macdef GL_OPERAND0_RGB = $extval (GLenum, "GL_OPERAND0_RGB")
macdef GL_OPERAND1_RGB = $extval (GLenum, "GL_OPERAND1_RGB")
macdef GL_OPERAND2_RGB = $extval (GLenum, "GL_OPERAND2_RGB")
macdef GL_OPERAND0_ALPHA = $extval (GLenum, "GL_OPERAND0_ALPHA")
macdef GL_OPERAND1_ALPHA = $extval (GLenum, "GL_OPERAND1_ALPHA")
macdef GL_OPERAND2_ALPHA = $extval (GLenum, "GL_OPERAND2_ALPHA")
macdef GL_RGB_SCALE = $extval (GLenum, "GL_RGB_SCALE")
macdef GL_ADD_SIGNED = $extval (GLenum, "GL_ADD_SIGNED")
macdef GL_INTERPOLATE = $extval (GLenum, "GL_INTERPOLATE")
macdef GL_SUBTRACT = $extval (GLenum, "GL_SUBTRACT")
macdef GL_CONSTANT = $extval (GLenum, "GL_CONSTANT")
macdef GL_PRIMARY_COLOR = $extval (GLenum, "GL_PRIMARY_COLOR")
macdef GL_PREVIOUS = $extval (GLenum, "GL_PREVIOUS")

// texture_env_dot3
macdef GL_DOT3_RGB = $extval (GLenum, "GL_DOT3_RGB")
macdef GL_DOT3_RGBA = $extval (GLenum, "GL_DOT3_RGBA")

// texture_border_clamp
macdef GL_CLAMP_TO_BORDER = $extval (GLenum, "GL_CLAMP_TO_BORDER")

(* ****** ****** *)

macdef GL_ARB_multitexture = $extval (GLenum, "GL_ARB_multitexture")
macdef GL_TEXTURE0_ARB = $extval (GLenum, "GL_TEXTURE0_ARB")
macdef GL_TEXTURE1_ARB = $extval (GLenum, "GL_TEXTURE1_ARB")
macdef GL_TEXTURE2_ARB = $extval (GLenum, "GL_TEXTURE2_ARB")
macdef GL_TEXTURE3_ARB = $extval (GLenum, "GL_TEXTURE3_ARB")
macdef GL_TEXTURE4_ARB = $extval (GLenum, "GL_TEXTURE4_ARB")
macdef GL_TEXTURE5_ARB = $extval (GLenum, "GL_TEXTURE5_ARB")
macdef GL_TEXTURE6_ARB = $extval (GLenum, "GL_TEXTURE6_ARB")
macdef GL_TEXTURE7_ARB = $extval (GLenum, "GL_TEXTURE7_ARB")
macdef GL_TEXTURE8_ARB = $extval (GLenum, "GL_TEXTURE8_ARB")
macdef GL_TEXTURE9_ARB = $extval (GLenum, "GL_TEXTURE9_ARB")
macdef GL_TEXTURE10_ARB = $extval (GLenum, "GL_TEXTURE10_ARB")
macdef GL_TEXTURE11_ARB = $extval (GLenum, "GL_TEXTURE11_ARB")
macdef GL_TEXTURE12_ARB = $extval (GLenum, "GL_TEXTURE12_ARB")
macdef GL_TEXTURE13_ARB = $extval (GLenum, "GL_TEXTURE13_ARB")
macdef GL_TEXTURE14_ARB = $extval (GLenum, "GL_TEXTURE14_ARB")
macdef GL_TEXTURE15_ARB = $extval (GLenum, "GL_TEXTURE15_ARB")
macdef GL_TEXTURE16_ARB = $extval (GLenum, "GL_TEXTURE16_ARB")
macdef GL_TEXTURE17_ARB = $extval (GLenum, "GL_TEXTURE17_ARB")
macdef GL_TEXTURE18_ARB = $extval (GLenum, "GL_TEXTURE18_ARB")
macdef GL_TEXTURE19_ARB = $extval (GLenum, "GL_TEXTURE19_ARB")
macdef GL_TEXTURE20_ARB = $extval (GLenum, "GL_TEXTURE20_ARB")
macdef GL_TEXTURE21_ARB = $extval (GLenum, "GL_TEXTURE21_ARB")
macdef GL_TEXTURE22_ARB = $extval (GLenum, "GL_TEXTURE22_ARB")
macdef GL_TEXTURE23_ARB = $extval (GLenum, "GL_TEXTURE23_ARB")
macdef GL_TEXTURE24_ARB = $extval (GLenum, "GL_TEXTURE24_ARB")
macdef GL_TEXTURE25_ARB = $extval (GLenum, "GL_TEXTURE25_ARB")
macdef GL_TEXTURE26_ARB = $extval (GLenum, "GL_TEXTURE26_ARB")
macdef GL_TEXTURE27_ARB = $extval (GLenum, "GL_TEXTURE27_ARB")
macdef GL_TEXTURE28_ARB = $extval (GLenum, "GL_TEXTURE28_ARB")
macdef GL_TEXTURE29_ARB = $extval (GLenum, "GL_TEXTURE29_ARB")
macdef GL_TEXTURE30_ARB = $extval (GLenum, "GL_TEXTURE30_ARB")
macdef GL_TEXTURE31_ARB = $extval (GLenum, "GL_TEXTURE31_ARB")
macdef GL_ACTIVE_TEXTURE_ARB = $extval (GLenum, "GL_ACTIVE_TEXTURE_ARB")
macdef GL_CLIENT_ACTIVE_TEXTURE_ARB = $extval (GLenum, "GL_CLIENT_ACTIVE_TEXTURE_ARB")
macdef GL_MAX_TEXTURE_UNITS_ARB = $extval (GLenum, "GL_MAX_TEXTURE_UNITS_ARB")
macdef GL_MESA_shader_debug = $extval (GLenum, "GL_MESA_shader_debug")
macdef GL_DEBUG_OBJECT_MESA = $extval (GLenum, "GL_DEBUG_OBJECT_MESA")
macdef GL_DEBUG_PRINT_MESA = $extval (GLenum, "GL_DEBUG_PRINT_MESA")
macdef GL_DEBUG_ASSERT_MESA = $extval (GLenum, "GL_DEBUG_ASSERT_MESA")
macdef GL_MESA_trace = $extval (GLenum, "GL_MESA_trace")
macdef GL_TRACE_ALL_BITS_MESA = $extval (GLenum, "GL_TRACE_ALL_BITS_MESA")
macdef GL_TRACE_OPERATIONS_BIT_MESA = $extval (GLenum, "GL_TRACE_OPERATIONS_BIT_MESA")
macdef GL_TRACE_PRIMITIVES_BIT_MESA = $extval (GLenum, "GL_TRACE_PRIMITIVES_BIT_MESA")
macdef GL_TRACE_ARRAYS_BIT_MESA = $extval (GLenum, "GL_TRACE_ARRAYS_BIT_MESA")
macdef GL_TRACE_TEXTURES_BIT_MESA = $extval (GLenum, "GL_TRACE_TEXTURES_BIT_MESA")
macdef GL_TRACE_PIXELS_BIT_MESA = $extval (GLenum, "GL_TRACE_PIXELS_BIT_MESA")
macdef GL_TRACE_ERRORS_BIT_MESA = $extval (GLenum, "GL_TRACE_ERRORS_BIT_MESA")
macdef GL_TRACE_MASK_MESA = $extval (GLenum, "GL_TRACE_MASK_MESA")
macdef GL_TRACE_NAME_MESA = $extval (GLenum, "GL_TRACE_NAME_MESA")
macdef GL_MESA_packed_depth_stencil = $extval (GLenum, "GL_MESA_packed_depth_stencil")
macdef GL_DEPTH_STENCIL_MESA = $extval (GLenum, "GL_DEPTH_STENCIL_MESA")
macdef GL_UNSIGNED_INT_24_8_MESA = $extval (GLenum, "GL_UNSIGNED_INT_24_8_MESA")
macdef GL_UNSIGNED_INT_8_24_REV_MESA = $extval (GLenum, "GL_UNSIGNED_INT_8_24_REV_MESA")
macdef GL_UNSIGNED_SHORT_15_1_MESA = $extval (GLenum, "GL_UNSIGNED_SHORT_15_1_MESA")
macdef GL_UNSIGNED_SHORT_1_15_REV_MESA = $extval (GLenum, "GL_UNSIGNED_SHORT_1_15_REV_MESA")
macdef GL_MESA_program_debug = $extval (GLenum, "GL_MESA_program_debug")
macdef GL_FRAGMENT_PROGRAM_POSITION_MESA = $extval (GLenum, "GL_FRAGMENT_PROGRAM_POSITION_MESA")
macdef GL_FRAGMENT_PROGRAM_CALLBACK_MESA = $extval (GLenum, "GL_FRAGMENT_PROGRAM_CALLBACK_MESA")
macdef GL_FRAGMENT_PROGRAM_CALLBACK_FUNC_MESA = $extval (GLenum, "GL_FRAGMENT_PROGRAM_CALLBACK_FUNC_MESA")
macdef GL_FRAGMENT_PROGRAM_CALLBACK_DATA_MESA = $extval (GLenum, "GL_FRAGMENT_PROGRAM_CALLBACK_DATA_MESA")
macdef GL_VERTEX_PROGRAM_POSITION_MESA = $extval (GLenum, "GL_VERTEX_PROGRAM_POSITION_MESA")
macdef GL_VERTEX_PROGRAM_CALLBACK_MESA = $extval (GLenum, "GL_VERTEX_PROGRAM_CALLBACK_MESA")
macdef GL_VERTEX_PROGRAM_CALLBACK_FUNC_MESA = $extval (GLenum, "GL_VERTEX_PROGRAM_CALLBACK_FUNC_MESA")
macdef GL_VERTEX_PROGRAM_CALLBACK_DATA_MESA = $extval (GLenum, "GL_VERTEX_PROGRAM_CALLBACK_DATA_MESA")
macdef GL_ATI_blend_equation_separate = $extval (GLenum, "GL_ATI_blend_equation_separate")
macdef GL_ALPHA_BLEND_EQUATION_ATI = $extval (GLenum, "GL_ALPHA_BLEND_EQUATION_ATI")

(* ****** ****** *)

(* end of [gl.sats] *)
