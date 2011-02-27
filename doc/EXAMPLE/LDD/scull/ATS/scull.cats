//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
/* ****** ****** */

#ifndef ATS_SCULL_CATS
#define ATS_SCULL_CATS

/* ****** ****** */

#include "contrib/kernel/include/ats_types.h"
#include "contrib/kernel/include/ats_basics.h"
#include "contrib/kernel/include/ats_memory.h"

/* ****** ****** */

#include "contrib/kernel/CATS/pointer.cats"
#include "contrib/kernel/CATS/sizetype.cats"

/* ****** ****** */

#include <linux/slab.h>
#include <linux/cdev.h>
#include <linux/semaphore.h>

#include "../scull.h"

typedef struct scull_dev scull_dev_struct ;
typedef struct scull_qset scull_qset_struct ;

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
