extern
ats_void_type gc_init () ;
extern
ats_void_type gc_markroot_bsz (ats_ptr_type ptr, size_t bsz) ;

//

extern
ats_ptr_type gcats0_malloc_err (ats_int_type nbyte) ;
extern
ats_ptr_type gcats0_malloc (ats_int_type nbyte) ;
extern
ats_ptr_type gcats0_calloc (ats_int_type nmemb, ats_int_type size) ;
extern
ats_void_type gcats0_free (ats_ptr_type ptr) ;
extern
ats_ptr_type gcats0_realloc (ats_ptr_type ptr, ats_int_type nbyte) ;

//

extern
ats_ptr_type gcats1_malloc (ats_int_type nbyte) ;
extern
ats_ptr_type gcats1_calloc (ats_int_type nmemb, ats_int_type size) ;
extern
ats_void_type gcats1_free (ats_ptr_type ptr) ;
extern
ats_ptr_type gcats1_realloc (ats_ptr_type ptr, ats_int_type nbyte) ;

