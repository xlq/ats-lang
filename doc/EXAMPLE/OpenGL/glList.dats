(*
**
** A simple implementation of the tetrix game
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Summer, 2008
**
*)

(* ****** ****** *)

abstype GLlistref

extern fun glListRef_make (): GLlistref = "atslib_glListRef_make"

extern fun glListRef_get
  (r: GLlistref): [n:nat] @(GLlist_v n | uint n)
  = "atslib_glListRef_get"

extern fun glListRef_set {n:nat}
  (pf: GLlist_v n | r: GLlistref, n: uint n): void
  = "atslib_glListRef_set"

extern fun glCallListRef (r: GLlistref): void = "atslib_glCallListRef"

%{^

static inline
ats_ptr_type atslib_glListRef_make () {
  uint *r ;
  r = ats_malloc_gc (sizeof(uint)) ; *r = (uint)0 ;
  return r ;
}

static inline
ats_uint_type
atslib_glListRef_get (ats_ptr_type r) {
  uint lst ;
  lst = *(uint*)r ;
  if (lst == 0) {
    fprintf (stderr, "Exit: [glListRef_get] failed.") ;
    exit (1) ;
  }
  *(uint*)r = (uint)0 ;
  return lst ;
}

static inline
ats_void_type
atslib_glListRef_set
  (ats_ptr_type r, ats_uint_type lst) {
  if (*(uint*)r != 0) {
    fprintf (stderr, "Exit: [glListRef_set] failed.") ;
    exit (1) ;
  }
  *(uint*)r = (uint)lst ;
  return ;
}

static inline
ats_void_type atslib_glCallListRef (ats_ptr_type r) {
  uint lst ;
  lst = *(ats_uint_type*)r ;
  if (lst == 0) {
    fprintf (stderr, "Exit: [glCallList(%u)] failed.\n", lst) ;
    exit (1) ;
  }
  glCallList (lst) ;
  return ;
}

%}
