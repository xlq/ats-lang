//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
/* ****** ****** */

#ifndef ATS_SCULL_CATS
#define ATS_SCULL_CATS

/* ****** ****** */

#include "contrib/linux/CATS/integer.cats"
#include "contrib/linux/CATS/pointer.cats"
#include "contrib/linux/CATS/sizetype.cats"

/* ****** ****** */

#include <linux/slab.h>
#include <linux/cdev.h>
#include <linux/semaphore.h>

#include "../scull.h"

typedef struct scull_dev scull_dev_struct ;
typedef struct scull_qset scull_qset_struct ;

/* ****** ****** */

typedef unsigned long int ulint ;
#define add_loff_int(x, y) (((ulint)x) + ((ulint)y))

/* ****** ****** */

#define scull_ptr_make_null() (NULL)

/* ****** ****** */

ATSinline()
ats_void_type
scull_qtmptr_free
  (ats_ptr_type p) {
  if (p) ATS_FREE(p) ; return ;
} // end of [scull_qtmptr_free]

/* ****** ****** */

ATSinline()
ats_ptr_type
scull_qset_alloc () {
  return ATS_MALLOC(sizeof(scull_qset_struct)) ;
} // end of [scull_qset_alloc]

ATSinline()
ats_void_type
scull_qset_free (ats_ptr_type p) { return ATS_FREE(p) ; }

/* ****** ****** */

ATSinline()
ats_ptr_type
scull_qset_get_next
  (ats_ptr_type p) {
  return ((scull_qset_struct*)p)->next ;
} // end of [scull_qset_get_next]

ATSinline()
ats_void_type
scull_qset_set_next (
  ats_ptr_type p, ats_ptr_type n
) {
  ((scull_qset_struct*)p)->next = n ; return ;
} // end of [scull_qset_set_next]

/* ****** ****** */

#endif // end of [ATS_SCULL_CATS]

/* ****** ****** */

/* end of [scull.cats] */
