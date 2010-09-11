#
#
# unit testing (kind of) for ATS library code
#
#

######

.PHONY: all
all:: checkall

checkall:: compall cleanall
	echo "[checkall] is finished successfully!"

######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc
ATSOPT=$(or $(ATSHOME), "/usr")/bin/atsopt

######

compall:: \
  prelude_array \
  prelude_array0 \
  prelude_bool \
  prelude_char \
  prelude_float \
  prelude_list \
  prelude_list_vt \
  prelude_matrix \
  prelude_matrix0 \
  prelude_string \
  libc_complex \
  libc_dirent \
  libc_dlfcn \
  libc_gmp \
  libc_sched \
  libc_stdlib \
  libats_funarray_braun \
  libats_funheap_braun \
  libats_funmap_avltree \
  libats_genarrays \
  libats_hashtable_chain \
  libats_hashtable_linprb \
  libats_intinf \
  libats_iterint \
  libats_linbitvec \
  libats_linmap_avltree \
  libats_linqueue_arr \
  libats_linqueue_lst \
  libats_linstack_arr \
  libats_regexp \
  libats_parworkshop \
  libats_smlbas_array \
  libats_smlbas_array2 \
  libats_smlbas_char \
  libats_smlbas_list \
  libats_smlbas_string \
  libats_smlbas_time \

######

prelude_array: prelude_array.dats
	$(ATSCC) -O2 -o prelude_array prelude_array.dats && ./prelude_array

prelude_array0: prelude_array0.dats
	$(ATSCC) -O2 -o prelude_array0 prelude_array0.dats && ./prelude_array0

prelude_bool: prelude_bool.dats
	$(ATSCC) -O2 -o prelude_bool prelude_bool.dats && ./prelude_bool

prelude_char: prelude_char.dats
	$(ATSCC) -O2 -o prelude_char prelude_char.dats && ./prelude_char

prelude_float: prelude_float.dats
	$(ATSCC) -O2 -o prelude_float prelude_float.dats && ./prelude_float

prelude_list: prelude_list.dats
	$(ATSCC) -O2 -o prelude_list prelude_list.dats && ./prelude_list

prelude_list_vt: prelude_list_vt.dats
	$(ATSCC) -O2 -o prelude_list_vt prelude_list_vt.dats && ./prelude_list_vt

prelude_matrix: prelude_matrix.dats
	$(ATSCC) -O2 -o prelude_matrix prelude_matrix.dats && ./prelude_matrix

prelude_matrix0: prelude_matrix0.dats
	$(ATSCC) -O2 -o prelude_matrix0 prelude_matrix0.dats && ./prelude_matrix0

prelude_string: prelude_string.dats
	$(ATSCC) -O2 -o prelude_string prelude_string.dats && ./prelude_string

######

libc_complex: libc_complex.dats
	$(ATSCC) -O2 -o libc_complex libc_complex.dats -lm && ./libc_complex

######

libc_dirent: libc_dirent.dats
	$(ATSCC) -O2 -o libc_dirent libc_dirent.dats && ./libc_dirent "."

libc_dlfcn: libc_dlfcn.dats
	$(ATSCC) -rdynamic -O2 -o libc_dlfcn libc_dlfcn.dats -ldl && ./libc_dlfcn "."

######

libc_gmp: libc_gmp.dats
	$(ATSCC) -D_GNU_SOURCE -O2 -o libc_gmp libc_gmp.dats -lgmp && ./libc_gmp

######

libc_sched: libc_sched.dats
	$(ATSCC) -D_GNU_SOURCE -O2 -o libc_sched libc_sched.dats && ./libc_sched

######

libc_stdlib: libc_stdlib.dats
	$(ATSCC) -O2 -o libc_stdlib libc_stdlib.dats && ./libc_stdlib

######

libats_funarray_braun: libats_funarray_braun.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_funarray_braun libats_funarray_braun.dats \
	&& ./libats_funarray_braun 0 1 2 3 4 5 6 7 8 9

######

libats_funheap_braun: libats_funheap_braun.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_funheap_braun libats_funheap_braun.dats \
	&& ./libats_funheap_braun 100000

######

libats_funmap_avltree: libats_funmap_avltree.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_funmap_avltree libats_funmap_avltree.dats \
     && ./libats_funmap_avltree 100000

######

libats_funralist_nested: libats_funralist_nested.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_funralist_nested libats_funralist_nested.dats \
	&& ./libats_funralist_nested 100000

######

libats_genarrays: libats_genarrays.dats
	$(ATSCC) -O2 -o libats_genarrays libats_genarrays.dats && ./libats_genarrays

######

libats_hashtable_chain: libats_hashtable_chain.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_hashtable_chain libats_hashtable_chain.dats \
     && ./libats_hashtable_chain 100000

libats_hashtable_linprb: libats_hashtable_linprb.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_hashtable_linprb libats_hashtable_linprb.dats \
     && ./libats_hashtable_linprb 100000

######

libats_intinf: libats_intinf.dats
	$(ATSCC) -O2 -o libats_intinf libats_intinf.dats -lgmp && ./libats_intinf 10

libats_iterint: libats_iterint.dats
	$(ATSCC) -O2 -o libats_iterint libats_iterint.dats && ./libats_iterint

######

libats_linbitvec: libats_linbitvec.dats
	$(ATSCC) -O2 -o libats_linbitvec libats_linbitvec.dats && ./libats_linbitvec

######

libats_linmap_avltree: libats_linmap_avltree.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_linmap_avltree libats_linmap_avltree.dats \
     && ./libats_linmap_avltree 100000

######

libats_linqueue_arr: libats_linqueue_arr.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_linqueue_arr libats_linqueue_arr.dats \
     && ./libats_linqueue_arr 1000000

######

libats_linqueue_lst: libats_linqueue_lst.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_linqueue_lst libats_linqueue_lst.dats \
     && ./libats_linqueue_lst 1000000

######

libats_linstack_arr: libats_linstack_arr.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_linstack_arr libats_linstack_arr.dats \
     && ./libats_linstack_arr 1000000

######

libats_regexp: libats_regexp.dats
	$(ATSCC) -O2 -o libats_regexp libats_regexp.dats -lpcre && ./libats_regexp "12345789"

######

libats_parworkshop: libats_parworkshop.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O2 -o libats_parworkshop libats_parworkshop.dats -lpthread -lats_mt \
     && ./libats_parworkshop

######

libats_smlbas_array: libats_smlbas_array.dats
	$(ATSCC) -O2 -o libats_smlbas_array libats_smlbas_array.dats -lats_smlbas \
     && ./libats_smlbas_array

libats_smlbas_array2: libats_smlbas_array2.dats
	$(ATSCC) -O2 -o libats_smlbas_array2 libats_smlbas_array2.dats -lats_smlbas \
     && ./libats_smlbas_array2

libats_smlbas_char: libats_smlbas_char.dats
	$(ATSCC) -O2 -o libats_smlbas_char libats_smlbas_char.dats -lats_smlbas \
     && ./libats_smlbas_char

libats_smlbas_list: libats_smlbas_list.dats
	$(ATSCC) -O2 -o libats_smlbas_list libats_smlbas_list.dats -lats_smlbas \
     && ./libats_smlbas_list

libats_smlbas_string: libats_smlbas_string.dats
	$(ATSCC) -O2 -o libats_smlbas_string libats_smlbas_string.dats -lats_smlbas \
     && ./libats_smlbas_string

libats_smlbas_time: libats_smlbas_time.dats
	$(ATSCC) -O2 -o libats_smlbas_time libats_smlbas_time.dats -lats_smlbas -lm \
     && ./libats_smlbas_time

######

clean::
	rm -f *~
	rm -f a.out *_?ats.c *_?ats.o

cleanall: clean
	rm -f prelude_array
	rm -f prelude_array0
	rm -f prelude_bool
	rm -f prelude_char
	rm -f prelude_float
	rm -f prelude_list
	rm -f prelude_list_vt
	rm -f prelude_matrix
	rm -f prelude_matrix0
	rm -f prelude_string
	rm -f libc_complex
	rm -f libc_dirent
	rm -f libc_dlfcn
	rm -f libc_gmp
	rm -f libc_sched
	rm -f libc_stdlib
	rm -f libats_funarray_braun
	rm -f libats_funheap_braun
	rm -f libats_funmap_avltree
	rm -f libats_funralist_nested
	rm -f libats_genarrays
	rm -f libats_hashtable_chain
	rm -f libats_hashtable_linprb
	rm -f libats_intinf
	rm -f libats_iterint
	rm -f libats_linbitvec
	rm -f libats_linmap_avltree
	rm -f libats_linqueue_arr
	rm -f libats_linqueue_lst
	rm -f libats_linstack_arr
	rm -f libats_regexp
	rm -f libats_parworkshop
	rm -f libats_smlbas_array
	rm -f libats_smlbas_array2
	rm -f libats_smlbas_char
	rm -f libats_smlbas_list
	rm -f libats_smlbas_string
	rm -f libats_smlbas_time

###### end of [Makefile] ######
