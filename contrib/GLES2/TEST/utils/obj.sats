(*
** Wavefront OBJ file loader based on the GLM library by Nate Robbins.
** Written by Artyom Shalkhakov, June 2011.
*)

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no staloading at run-time

(* ****** ****** *)

typedef float2_t = @(float, float)
typedef float3_t = @(float, float, float)
typedef size3_t = @(size_t, size_t, size_t)
// zero-based!
typedef faceidx = @{vidx= size_t, nidx= size_t, tidx= size_t}
viewtypedef triangle = @(faceidx, faceidx, faceidx)

(* ****** ****** *)

viewtypedef arrsz_vt (a:t@ype, n:int, l:addr) =
  @(array_v (a, n, l), free_gc_v (a, n, l) | size_t n, ptr l)
// end of [arrsz_vt]

viewtypedef arrsz_vt (a:t@ype, n:int) = [l:addr] arrsz_vt (a, n, l)
viewtypedef arrsz0_vt (a:t@ype) = arrsz_vt (a, 0, null)

(* ****** ****** *)

viewtypedef mesh (nv:int, nn:int, ntc:int, nf:int) = @{
  verts= arrsz_vt (float3_t, nv)
, norms= arrsz_vt (float3_t, nn)
, texcoords= arrsz_vt (float2_t, ntc)
, faces= arrsz_vt (triangle, nf)
} // end of [mesh]

viewtypedef mesh = [nv,nn,ntc,nf:nat] mesh (nv, nn, ntc, nf)

viewtypedef mesh0 = @{
  verts= arrsz0_vt float3_t
, norms= arrsz0_vt float3_t
, texcoords= arrsz0_vt float2_t
, faces= arrsz0_vt triangle
} // end of [mesh0]

(* ****** ****** *)

// may throw an exception
fun mesh_from_file (
 name: string, m: &mesh0? >> mesh
) : void

fun mesh_free (m: mesh): void

(* ****** ****** *)

(* end of [obj.sats] *)
