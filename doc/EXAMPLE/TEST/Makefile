#
#
# unit testing (kind of) for ATS library code
#
#

######

ATSHOMEQ="$(ATSHOME)"
ifeq ($(ATSHOMEQ),"")
ATSHOMEQ="/usr" # default value if [ATSHOME] is undefined
endif

######

ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

.PHONY: all
all:: checkall

checkall:: compall cleanall
	echo "[checkall] is finished successfully!"

######

compall:: prelude_array
prelude_array: prelude_array.dats
	$(ATSCC) -O2 -o prelude_array prelude_array.dats && ./prelude_array

compall:: prelude_array0
prelude_array0: prelude_array0.dats
	$(ATSCC) -O2 -o prelude_array0 prelude_array0.dats && ./prelude_array0

compall:: prelude_bool
prelude_bool: prelude_bool.dats
	$(ATSCC) -O2 -o prelude_bool prelude_bool.dats && ./prelude_bool

compall:: prelude_char
prelude_char: prelude_char.dats
	$(ATSCC) -O2 -o prelude_char prelude_char.dats && ./prelude_char

compall:: prelude_float
prelude_float: prelude_float.dats
	$(ATSCC) -O2 -o prelude_float prelude_float.dats && ./prelude_float

compall:: prelude_list
prelude_list: prelude_list.dats
	$(ATSCC) -O2 -o prelude_list prelude_list.dats && ./prelude_list

compall:: prelude_list_vt
prelude_list_vt: prelude_list_vt.dats
	$(ATSCC) -O2 -o prelude_list_vt prelude_list_vt.dats && ./prelude_list_vt

compall:: prelude_matrix
prelude_matrix: prelude_matrix.dats
	$(ATSCC) -O2 -o prelude_matrix prelude_matrix.dats && ./prelude_matrix

compall:: prelude_matrix0
prelude_matrix0: prelude_matrix0.dats
	$(ATSCC) -O2 -o prelude_matrix0 prelude_matrix0.dats && ./prelude_matrix0

compall:: prelude_string
prelude_string: prelude_string.dats
	$(ATSCC) -O2 -o prelude_string prelude_string.dats && ./prelude_string

######

compall:: libc_complex
libc_complex: libc_complex.dats
	$(ATSCC) -O2 -o libc_complex libc_complex.dats -lm && ./libc_complex

######

compall:: libc_dirent
libc_dirent: libc_dirent.dats
	$(ATSCC) -O2 -o libc_dirent libc_dirent.dats && ./libc_dirent "."

compall:: libc_dlfcn
libc_dlfcn: libc_dlfcn.dats
	$(ATSCC) -rdynamic -O2 -o libc_dlfcn libc_dlfcn.dats -ldl && ./libc_dlfcn "."

######

compall:: libc_gmp
libc_gmp: libc_gmp.dats
	$(ATSCC) -D_GNU_SOURCE -O2 -o libc_gmp libc_gmp.dats -lats -lgmp && ./libc_gmp

######

compall:: libc_printf
libc_printf: libc_printf.dats
	$(ATSCC) -o libc_printf libc_printf.dats && ./libc_printf

######

compall:: libc_pwd
libc_pwd: libc_pwd.dats
	$(ATSCC) -O2 -o libc_pwd libc_pwd.dats && ./libc_pwd

######

compall:: libc_random
libc_random: libc_random.dats
	$(ATSCC) -O2 -o libc_random libc_random.dats && ./libc_random

######

compall:: libc_sched
libc_sched: libc_sched.dats
	$(ATSCC) -D_GNU_SOURCE -O2 -o libc_sched libc_sched.dats && ./libc_sched

######

compall:: libc_stdio
libc_stdio: libc_stdio.dats ; $(ATSCC) -O2 -o $@ $< && ./libc_stdio

compall:: libc_stdlib
libc_stdlib: libc_stdlib.dats ; $(ATSCC) -O2 -o $@ $< && ./libc_stdlib

######

compall:: libc_time
libc_time: libc_time.dats
	$(ATSCC) -D_XOPEN_SOURCE -O2 -o $@ $< && ./libc_time

######

compall:: libc_unistd
libc_unistd: libc_unistd.dats ; $(ATSCC) -O2 -o $@ $< && ./libc_unistd

######

compall:: libc_sys_utsname
libc_sys_utsname: libc_sys_utsname.dats ; $(ATSCC) -O2 -o $@ $< && ./libc_sys_utsname

######

compall:: libats_funarray_braun
libats_funarray_braun: libats_funarray_braun.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_funarray_braun libats_funarray_braun.dats \
	&& ./libats_funarray_braun 0 1 2 3 4 5 6 7 8 9

######

compall:: libats_fundeque_fingertree
libats_fundeque_fingertree: libats_fundeque_fingertree.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_fundeque_fingertree libats_fundeque_fingertree.dats \
	&& ./libats_fundeque_fingertree 10

######

compall:: libats_funheap_braun
libats_funheap_braun: libats_funheap_braun.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_funheap_braun libats_funheap_braun.dats \
	&& ./libats_funheap_braun 100000

######

compall:: libats_funmap_avltree
libats_funmap_avltree: libats_funmap_avltree.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_funmap_avltree libats_funmap_avltree.dats \
     && ./libats_funmap_avltree 100000

######

compall:: libats_funralist_nested
libats_funralist_nested: libats_funralist_nested.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_funralist_nested libats_funralist_nested.dats \
	&& ./libats_funralist_nested 100000

######

compall:: libats_genarrays
libats_genarrays: libats_genarrays.dats
	$(ATSCC) -O2 -o libats_genarrays libats_genarrays.dats && ./libats_genarrays

######

compall:: libats_hashtable_chain
libats_hashtable_chain: libats_hashtable_chain.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_hashtable_chain libats_hashtable_chain.dats \
     && ./libats_hashtable_chain 100000

compall:: libats_hashtable_linprb
libats_hashtable_linprb: libats_hashtable_linprb.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_hashtable_linprb libats_hashtable_linprb.dats \
     && ./libats_hashtable_linprb 100000

######

compall:: libats_intinf
libats_intinf: libats_intinf.dats
	$(ATSCC) -O2 -o libats_intinf libats_intinf.dats -lats -lgmp && ./libats_intinf 10

compall:: libats_iterint
libats_iterint: libats_iterint.dats
	$(ATSCC) -O2 -o libats_iterint libats_iterint.dats && ./libats_iterint

######

compall:: libats_linbitvec
libats_linbitvec: libats_linbitvec.dats
	$(ATSCC) -O2 -o libats_linbitvec libats_linbitvec.dats && ./libats_linbitvec

######

compall:: libats_linmap_avltree
libats_linmap_avltree: libats_linmap_avltree.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_linmap_avltree libats_linmap_avltree.dats \
     && ./libats_linmap_avltree 100000

######

compall:: libats_linqueue_arr
libats_linqueue_arr: libats_linqueue_arr.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_linqueue_arr libats_linqueue_arr.dats \
     && ./libats_linqueue_arr 1000000

######

compall:: libats_linqueue_lst
libats_linqueue_lst: libats_linqueue_lst.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_linqueue_lst libats_linqueue_lst.dats \
     && ./libats_linqueue_lst 1000000

######

compall:: libats_linstack_arr
libats_linstack_arr: libats_linstack_arr.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_linstack_arr libats_linstack_arr.dats \
     && ./libats_linstack_arr 1000000

######

compall:: libats_parworkshop
libats_parworkshop: libats_parworkshop.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O2 -o libats_parworkshop libats_parworkshop.dats -lpthread -lats_mt \
     && ./libats_parworkshop

######

compall:: libats_rarray
libats_rarray: libats_rarray.dats
	$(ATSCC) -O2 -o libats_rarray libats_rarray.dats && ./libats_rarray

######

compall:: libats_regexp
libats_regexp: libats_regexp.dats
	$(ATSCC) -O2 -o libats_regexp libats_regexp.dats -lats -lpcre && ./libats_regexp "12345789"

######

compall:: libats_vector
libats_vector: libats_vector.dats
	$(ATSCC) -O2 -o libats_vector libats_vector.dats && ./libats_vector

######

compall:: libats_smlbas_array
libats_smlbas_array: libats_smlbas_array.dats
	$(ATSCC) -O2 -o libats_smlbas_array libats_smlbas_array.dats -lats_smlbas \
     && ./libats_smlbas_array

compall:: libats_smlbas_array2
libats_smlbas_array2: libats_smlbas_array2.dats
	$(ATSCC) -O2 -o libats_smlbas_array2 libats_smlbas_array2.dats -lats_smlbas \
     && ./libats_smlbas_array2

compall:: libats_smlbas_char
libats_smlbas_char: libats_smlbas_char.dats
	$(ATSCC) -O2 -o libats_smlbas_char libats_smlbas_char.dats -lats_smlbas \
     && ./libats_smlbas_char

compall:: libats_smlbas_list
libats_smlbas_list: libats_smlbas_list.dats
	$(ATSCC) -O2 -o libats_smlbas_list libats_smlbas_list.dats -lats_smlbas \
     && ./libats_smlbas_list

compall:: libats_smlbas_string
libats_smlbas_string: libats_smlbas_string.dats
	$(ATSCC) -O2 -o libats_smlbas_string libats_smlbas_string.dats -lats_smlbas \
     && ./libats_smlbas_string

compall:: libats_smlbas_time
libats_smlbas_time: libats_smlbas_time.dats
	$(ATSCC) -O2 -o libats_smlbas_time libats_smlbas_time.dats -lats_smlbas -lm \
     && ./libats_smlbas_time

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall: clean
	$(RMF) prelude_array
	$(RMF) prelude_array0
	$(RMF) prelude_bool
	$(RMF) prelude_char
	$(RMF) prelude_float
	$(RMF) prelude_list
	$(RMF) prelude_list_vt
	$(RMF) prelude_matrix
	$(RMF) prelude_matrix0
	$(RMF) prelude_string
	$(RMF) libc_complex
	$(RMF) libc_dirent
	$(RMF) libc_dlfcn
	$(RMF) libc_gmp
	$(RMF) libc_printf
	$(RMF) libc_pwd
	$(RMF) libc_random
	$(RMF) libc_sched
	$(RMF) libc_stdio
	$(RMF) libc_stdlib
	$(RMF) libc_time
	$(RMF) libc_unistd
	$(RMF) libc_sys_utsname
	$(RMF) libats_funarray_braun
	$(RMF) libats_fundeque_fingertree
	$(RMF) libats_funheap_braun
	$(RMF) libats_funmap_avltree
	$(RMF) libats_funralist_nested
	$(RMF) libats_genarrays
	$(RMF) libats_hashtable_chain
	$(RMF) libats_hashtable_linprb
	$(RMF) libats_intinf
	$(RMF) libats_iterint
	$(RMF) libats_linbitvec
	$(RMF) libats_linmap_avltree
	$(RMF) libats_linqueue_arr
	$(RMF) libats_linqueue_lst
	$(RMF) libats_linstack_arr
	$(RMF) libats_rarray
	$(RMF) libats_regexp
	$(RMF) libats_parworkshop
	$(RMF) libats_vector
	$(RMF) libats_smlbas_array
	$(RMF) libats_smlbas_array2
	$(RMF) libats_smlbas_char
	$(RMF) libats_smlbas_list
	$(RMF) libats_smlbas_string
	$(RMF) libats_smlbas_time

###### end of [Makefile] ######
