/*
 *
 * The following C code is generated by ATS/Anairiats
 * The compilation time is: 2009-1-15: 17h: 5m
 *
 */

/* include some .h files */
#include "ats_basics.h"
#include "ats_exception.h"
#include "ats_memory.h"
#include "ats_types.h"

/* include some .cats files */
#ifndef _ATS_PRELUDE_NONE
#include "prelude/CATS/array.cats"
#include "prelude/CATS/basics.cats"
#include "prelude/CATS/bool.cats"
#include "prelude/CATS/byte.cats"
#include "prelude/CATS/char.cats"
#include "prelude/CATS/float.cats"
#include "prelude/CATS/integer.cats"
#include "prelude/CATS/lazy.cats"
#include "prelude/CATS/lazy_vt.cats"
#include "prelude/CATS/pointer.cats"
#include "prelude/CATS/printf.cats"
#include "prelude/CATS/reference.cats"
#include "prelude/CATS/sizetype.cats"
#include "prelude/CATS/string.cats"
#include "prelude/CATS/array.cats"
#include "prelude/CATS/list.cats"
#include "prelude/CATS/option.cats"
#endif /* _ATS_PRELUDE_NONE */
/* prologue from statically loaded files */
/* external codes at top */
/* type definitions */
/* external typedefs */
/* external dynamic constructor declarations */
/* external dynamic constant declarations */
extern ats_void_type atspre_print_newline () ;
extern ats_void_type atspre_print_string (ats_ptr_type) ;

/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */

/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

ats_void_type
mainats () {
/* local vardec */
ATSlocal_void (tmp0) ;
ATSlocal_void (tmp1) ;

__ats_lab_mainats:
/* tmp1 = */ atspre_print_string ("Hello, world!") ;
/* tmp0 = */ atspre_print_newline () ;
return /* (tmp0) */ ;
} /* end of [mainats] */

/* static load function */

#ifndef _ATS_STALOADFUN_NONE

static int _2fusr_2fshare_2fatshome_2fdoc_2fEXAMPLE_2fINTRO_2fHelloWorld_2edats__staload_flag = 0 ;

ats_void_type _2fusr_2fshare_2fatshome_2fdoc_2fEXAMPLE_2fINTRO_2fHelloWorld_2edats__staload () {
if (_2fusr_2fshare_2fatshome_2fdoc_2fEXAMPLE_2fINTRO_2fHelloWorld_2edats__staload_flag) return ;
_2fusr_2fshare_2fatshome_2fdoc_2fEXAMPLE_2fINTRO_2fHelloWorld_2edats__staload_flag = 1 ;
return ;
} /* staload function */

#endif // [_ATS_STALOADFUN_NONE]

/* dynamic load function */

#ifndef _ATS_DYNLOADFUN_NONE

// extern int _2fusr_2fshare_2fatshome_2fdoc_2fEXAMPLE_2fINTRO_2fHelloWorld_2edats__dynload_flag ;

ats_void_type _2fusr_2fshare_2fatshome_2fdoc_2fEXAMPLE_2fINTRO_2fHelloWorld_2edats__dynload () {
// _2fusr_2fshare_2fatshome_2fdoc_2fEXAMPLE_2fINTRO_2fHelloWorld_2edats__dynload_flag = 1 ;
_2fusr_2fshare_2fatshome_2fdoc_2fEXAMPLE_2fINTRO_2fHelloWorld_2edats__staload () ;

/* marking static variables for GC */

/* marking external values for GC */

/* code for dynamic loading */
return ;
} /* dynload function */

#endif // [_ATS_DYNLOADFUN_NONE]

int main (int argc, char *argv[]) {
ATS_GC_INIT() ;
mainats_prelude() ;

#ifndef _ATS_DYNLOADFUN_NONE
_2fusr_2fshare_2fatshome_2fdoc_2fEXAMPLE_2fINTRO_2fHelloWorld_2edats__dynload () ;
#endif

mainats ((ats_int_type)argc, (ats_ptr_type)argv) ;
return (0) ;
} /* end of main */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [HelloWorld_dats.c] */
