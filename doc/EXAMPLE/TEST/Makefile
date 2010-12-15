#
#
# (kind of) unit testing for ATS library code
#
#

######

ATSUSRQ="$(ATSHOME)"
ifeq ($(ATSUSRQ),"")
ATSUSRQ="/usr"
endif

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSOPT=$(ATSUSRQ)/bin/atsopt

######

.PHONY: all
all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean

######

checkall:: prelude_array
prelude_array: prelude_array.dats
	$(ATSCC) -O2 -o prelude_array prelude_array.dats && ./prelude_array
cleanall:: ; $(RMF) prelude_array

checkall:: prelude_array0
prelude_array0: prelude_array0.dats
	$(ATSCC) -O2 -o prelude_array0 prelude_array0.dats && ./prelude_array0
cleanall:: ; $(RMF) prelude_array0

checkall:: prelude_bool
prelude_bool: prelude_bool.dats
	$(ATSCC) -O2 -o prelude_bool prelude_bool.dats && ./prelude_bool
cleanall:: ; $(RMF) prelude_bool

checkall:: prelude_char
prelude_char: prelude_char.dats
	$(ATSCC) -O2 -o prelude_char prelude_char.dats && ./prelude_char
cleanall:: ; $(RMF) prelude_char

checkall:: prelude_float
prelude_float: prelude_float.dats
	$(ATSCC) -O2 -o prelude_float prelude_float.dats && ./prelude_float
cleanall:: ; $(RMF) prelude_float

checkall:: prelude_list
prelude_list: prelude_list.dats
	$(ATSCC) -O2 -o prelude_list prelude_list.dats && ./prelude_list
cleanall:: ; $(RMF) prelude_list

checkall:: prelude_list_vt
prelude_list_vt: prelude_list_vt.dats
	$(ATSCC) -O2 -o prelude_list_vt prelude_list_vt.dats && ./prelude_list_vt
cleanall:: ; $(RMF) prelude_list_vt

checkall:: prelude_matrix
prelude_matrix: prelude_matrix.dats
	$(ATSCC) -O2 -o prelude_matrix prelude_matrix.dats && ./prelude_matrix
cleanall:: ; $(RMF) prelude_matrix

checkall:: prelude_matrix0
prelude_matrix0: prelude_matrix0.dats
	$(ATSCC) -O2 -o prelude_matrix0 prelude_matrix0.dats && ./prelude_matrix0
cleanall:: ; $(RMF) prelude_matrix0

checkall:: prelude_string
prelude_string: prelude_string.dats
	$(ATSCC) -O2 -o prelude_string prelude_string.dats && ./prelude_string
cleanall:: ; $(RMF) prelude_string

######

checkall:: libc_complex
libc_complex: libc_complex.dats
	$(ATSCC) -O2 -o libc_complex libc_complex.dats -lm && ./libc_complex
cleanall:: ; $(RMF) libc_complex

######

checkall:: libc_dirent
libc_dirent: libc_dirent.dats
	$(ATSCC) -O2 -o libc_dirent libc_dirent.dats && ./libc_dirent "."
cleanall:: ; $(RMF) libc_dirent

checkall:: libc_dlfcn
libc_dlfcn: libc_dlfcn.dats
	$(ATSCC) -rdynamic -O2 -o libc_dlfcn libc_dlfcn.dats -ldl && ./libc_dlfcn "."
cleanall:: ; $(RMF) libc_dlfcn

######

checkall:: libc_gmp
libc_gmp: libc_gmp.dats
	$(ATSCC) -D_GNU_SOURCE -O2 -o libc_gmp libc_gmp.dats -lats -lgmp && ./libc_gmp
cleanall:: ; $(RMF) libc_gmp

######

checkall:: libc_printf
libc_printf: libc_printf.dats
	$(ATSCC) -o libc_printf libc_printf.dats && ./libc_printf
cleanall:: ; $(RMF) libc_printf

######

checkall:: libc_pwd
libc_pwd: libc_pwd.dats
	$(ATSCC) -O2 -o libc_pwd libc_pwd.dats && ./libc_pwd
cleanall:: ; $(RMF) libc_pwd

######

checkall:: libc_random
libc_random: libc_random.dats
	$(ATSCC) -O2 -o libc_random libc_random.dats && ./libc_random
cleanall:: ; $(RMF) libc_random

######

checkall:: libc_sched
libc_sched: libc_sched.dats
	$(ATSCC) -D_GNU_SOURCE -O2 -o libc_sched libc_sched.dats && ./libc_sched
cleanall:: ; $(RMF) libc_sched

######

checkall:: libc_stdio
libc_stdio: libc_stdio.dats ; $(ATSCC) -O2 -o $@ $< && ./libc_stdio
cleanall:: ; $(RMF) libc_stdio

checkall:: libc_stdlib
libc_stdlib: libc_stdlib.dats ; $(ATSCC) -O2 -o $@ $< && ./libc_stdlib
cleanall:: ; $(RMF) libc_stdlib

######

checkall:: libc_time
libc_time: libc_time.dats
	$(ATSCC) -D_XOPEN_SOURCE -O2 -o $@ $< && ./libc_time
cleanall:: ; $(RMF) libc_time

######

checkall:: libc_unistd
libc_unistd: libc_unistd.dats ; $(ATSCC) -O2 -o $@ $< && ./libc_unistd
cleanall:: ; $(RMF) libc_unistd

######


checkall:: libc_sys_utsname
libc_sys_utsname: libc_sys_utsname.dats ; $(ATSCC) -O2 -o $@ $< && ./libc_sys_utsname
cleanall:: ; $(RMF) libc_sys_utsname

######


checkall:: libats_funarray_braun
libats_funarray_braun: libats_funarray_braun.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_funarray_braun libats_funarray_braun.dats \
     && ./libats_funarray_braun 0 1 2 3 4 5 6 7 8 9
cleanall:: ; $(RMF) libats_funarray_braun

######

checkall:: libats_fundeque_fingertree
libats_fundeque_fingertree: libats_fundeque_fingertree.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_fundeque_fingertree libats_fundeque_fingertree.dats \
     && ./libats_fundeque_fingertree 10
cleanall:: ; $(RMF) libats_fundeque_fingertree

######

checkall:: libats_funheap_braun
libats_funheap_braun: libats_funheap_braun.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_funheap_braun libats_funheap_braun.dats \
    && ./libats_funheap_braun 100000
cleanall:: ; $(RMF) libats_funheap_braun

######

checkall:: libats_funmap_avltree
libats_funmap_avltree: libats_funmap_avltree.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_funmap_avltree libats_funmap_avltree.dats \
     && ./libats_funmap_avltree 100000
cleanall:: ; $(RMF) libats_funmap_avltree


######

checkall:: libats_funralist_nested
libats_funralist_nested: libats_funralist_nested.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_funralist_nested libats_funralist_nested.dats \
     && ./libats_funralist_nested 100000
cleanall:: ; $(RMF) libats_funralist_nested

######

checkall:: libats_genarrays
libats_genarrays: libats_genarrays.dats
	$(ATSCC) -O2 -o libats_genarrays libats_genarrays.dats && ./libats_genarrays
cleanall:: ; $(RMF) libats_genarrays

######

checkall:: libats_hashtable_chain
libats_hashtable_chain: libats_hashtable_chain.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_hashtable_chain libats_hashtable_chain.dats \
     && ./libats_hashtable_chain 100000
cleanall:: ; $(RMF) libats_hashtable_chain

checkall:: libats_hashtable_linprb
libats_hashtable_linprb: libats_hashtable_linprb.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_hashtable_linprb libats_hashtable_linprb.dats \
     && ./libats_hashtable_linprb 100000
cleanall:: ; $(RMF) libats_hashtable_linprb

######

checkall:: libats_intinf
libats_intinf: libats_intinf.dats
	$(ATSCC) -O2 -o libats_intinf libats_intinf.dats -lats -lgmp && ./libats_intinf 10
cleanall:: ; $(RMF) libats_intinf

checkall:: libats_iterint
libats_iterint: libats_iterint.dats
	$(ATSCC) -O2 -o libats_iterint libats_iterint.dats && ./libats_iterint
cleanall:: ; $(RMF) libats_iterint

######

checkall:: libats_linbitvec
libats_linbitvec: libats_linbitvec.dats
	$(ATSCC) -O2 -o libats_linbitvec libats_linbitvec.dats && ./libats_linbitvec
cleanall:: ; $(RMF) libats_linbitvec

######

checkall:: libats_linmap_avltree
libats_linmap_avltree: libats_linmap_avltree.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_linmap_avltree libats_linmap_avltree.dats \
     && ./libats_linmap_avltree 100000
cleanall:: ; $(RMF) libats_linmap_avltree

######

checkall:: libats_linqueue_arr
libats_linqueue_arr: libats_linqueue_arr.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_linqueue_arr libats_linqueue_arr.dats \
     && ./libats_linqueue_arr 1000000
cleanall:: ; $(RMF) libats_linqueue_arr

######

checkall:: libats_linqueue_lst
libats_linqueue_lst: libats_linqueue_lst.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_linqueue_lst libats_linqueue_lst.dats \
     && ./libats_linqueue_lst 1000000
cleanall:: ; $(RMF) libats_linqueue_lst

######

checkall:: libats_linstack_arr
libats_linstack_arr: libats_linstack_arr.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_linstack_arr libats_linstack_arr.dats \
     && ./libats_linstack_arr 1000000
cleanall:: ; $(RMF) libats_linstack_arr

######

checkall:: libats_parworkshop
libats_parworkshop: libats_parworkshop.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O2 -o libats_parworkshop libats_parworkshop.dats -lpthread -lats_mt \
     && ./libats_parworkshop
cleanall:: ; $(RMF) libats_parworkshop

######

checkall:: libats_rarray
libats_rarray: libats_rarray.dats
	$(ATSCC) -O2 -o libats_rarray libats_rarray.dats && ./libats_rarray
cleanall:: ; $(RMF) libats_rarray

######

checkall:: libats_regexp
libats_regexp: libats_regexp.dats
	$(ATSCC) -O2 -o libats_regexp libats_regexp.dats -lats -lpcre && ./libats_regexp "12345789"
cleanall:: ; $(RMF) libats_regexp

######

checkall:: libats_vector
libats_vector: libats_vector.dats
	$(ATSCC) -O2 -o libats_vector libats_vector.dats && ./libats_vector
cleanall:: ; $(RMF) libats_vector

######

checkall:: libats_smlbas_array
libats_smlbas_array: libats_smlbas_array.dats
	$(ATSCC) -O2 -o libats_smlbas_array libats_smlbas_array.dats -lats_smlbas \
     && ./libats_smlbas_array
cleanall:: ; $(RMF) libats_smlbas_array

checkall:: libats_smlbas_array2
libats_smlbas_array2: libats_smlbas_array2.dats
	$(ATSCC) -O2 -o libats_smlbas_array2 libats_smlbas_array2.dats -lats_smlbas \
     && ./libats_smlbas_array2
cleanall:: ; $(RMF) libats_smlbas_array2

checkall:: libats_smlbas_char
libats_smlbas_char: libats_smlbas_char.dats
	$(ATSCC) -O2 -o libats_smlbas_char libats_smlbas_char.dats -lats_smlbas \
     && ./libats_smlbas_char
cleanall:: ; $(RMF) libats_smlbas_char

checkall:: libats_smlbas_list
libats_smlbas_list: libats_smlbas_list.dats
	$(ATSCC) -O2 -o libats_smlbas_list libats_smlbas_list.dats -lats_smlbas \
     && ./libats_smlbas_list
cleanall:: ; $(RMF) libats_smlbas_list

checkall:: libats_smlbas_string
libats_smlbas_string: libats_smlbas_string.dats
	$(ATSCC) -O2 -o libats_smlbas_string libats_smlbas_string.dats -lats_smlbas \
     && ./libats_smlbas_string
cleanall:: ; $(RMF) libats_smlbas_string

checkall:: libats_smlbas_time
libats_smlbas_time: libats_smlbas_time.dats
	$(ATSCC) -O2 -o libats_smlbas_time libats_smlbas_time.dats -lats_smlbas -lm \
     && ./libats_smlbas_time
cleanall:: ; $(RMF) libats_smlbas_time

######

RMF=rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

###### end of [Makefile] ######
