/*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*/

/* ****** ****** */

//
// some library functions for the Tiger programming language
//

/* ****** ****** */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* ****** ****** */

void*
tiger_array_make_elt (size_t asz, void *elt) {
  int i ;
  void **p0_arr, **p_arr ;
/*
  fprintf
    (stderr, "tiger_array_make_elt: asz = %li\n", asz) ;
  fprintf
    (stderr, "tiger_array_make_elt: elt = %li\n", elt) ;
*/
  p0_arr = p_arr = (void**)malloc(asz * sizeof(void*)) ;
  for (i = 0; i < asz; i += 1) *p_arr++ = elt ;
  return p0_arr ;
} /* tiger_array_make_elt */

void
tiger_flush () {
  fflush (stdout) ; return ;
} /* tiger_flush */

void
tiger_print (char *str) {
  fprintf (stdout, "%s", str) ; return ;
} /* tiger_print */

void
tiger_print_int (intptr_t i) {
  fprintf (stdout, "%li", i) ; return ;
} /* tiger_print_int */

/* ****** ****** */

int main () {
  tiger_main () ; return 0 ;
}

/* ****** ****** */

/* end of [tiger_prelude.c] */
