#
#
# unit testing (kind of)
#
#

######

checkall: compall cleanall
	echo "[checkall] is finished successfully!"

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

######

compall:: \
  prelude_array \
  prelude_array0 \
  prelude_list \
  prelude_list_vt \
  prelude_matrix \
  prelude_matrix0 \
  prelude_string \
  libc_dirent \
  libc_dlfcn \
  libc_stdlib \
  libats_funmap_avltree \
  libats_genarrays \
  libats_hashtable_chain \
  libats_hashtable_linprb \
  libats_intinf \
  libats_iterint \
  libats_linmap_avltree \
  libats_regexp \
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

libc_dirent: libc_dirent.dats
	$(ATSCC) -O2 -o libc_dirent libc_dirent.dats && ./libc_dirent "."

libc_dlfcn: libc_dlfcn.dats
	$(ATSCC) -rdynamic -O2 -o libc_dlfcn libc_dlfcn.dats -ldl && ./libc_dlfcn "."

libc_stdlib: libc_stdlib.dats
	$(ATSCC) -O2 -o libc_stdlib libc_stdlib.dats && ./libc_stdlib

######

libats_funmap_avltree: libats_funmap_avltree.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_funmap_avltree libats_funmap_avltree.dats \
     && ./libats_funmap_avltree 1000000

######

libats_genarrays: libats_genarrays.dats
	$(ATSCC) -O2 -o libats_genarrays libats_genarrays.dats && ./libats_genarrays

######

libats_hashtable_chain: libats_hashtable_chain.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_hashtable_chain libats_hashtable_chain.dats \
     && ./libats_hashtable_chain 1000000

libats_hashtable_linprb: libats_hashtable_linprb.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_hashtable_linprb libats_hashtable_linprb.dats \
     && ./libats_hashtable_linprb 1000000

######

libats_intinf: libats_intinf.dats
	$(ATSCC) -O2 -o libats_intinf libats_intinf.dats -lgmp && ./libats_intinf 10

libats_iterint: libats_iterint.dats
	$(ATSCC) -O2 -o libats_iterint libats_iterint.dats && ./libats_iterint

######

libats_linmap_avltree: libats_linmap_avltree.dats
	$(ATSCC) -D_ATS_GCATS -O2 -o libats_linmap_avltree libats_linmap_avltree.dats \
     && ./libats_linmap_avltree 1000000

######

libats_regexp: libats_regexp.dats
	$(ATSCC) -O2 -o libats_regexp libats_regexp.dats -lpcre && ./libats_regexp "12345789"

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
	rm -f prelude_list
	rm -f prelude_list_vt
	rm -f prelude_matrix
	rm -f prelude_matrix0
	rm -f prelude_string
	rm -f libc_dirent
	rm -f libc_dlfcn
	rm -f libc_stdlib
	rm -f libats_funmap
	rm -f libats_genarrays
	rm -f libats_hashtable_chain
	rm -f libats_hashtable_linprb
	rm -f libats_intinf
	rm -f libats_iterint
	rm -f libats_linmap
	rm -f libats_regexp
	rm -f libats_smlbas_array
	rm -f libats_smlbas_array2
	rm -f libats_smlbas_char
	rm -f libats_smlbas_list
	rm -f libats_smlbas_string
	rm -f libats_smlbas_time

###### end of [Makefile] ######
