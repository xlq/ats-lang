all:: \
  prelude_list \
  prelude_string \
  libc_dirent \
  libats_intinf \
  libats_regexp \

######

prelude_list: prelude_list.dats
	atscc -O2 -o prelude_list prelude_list.dats

prelude_string: prelude_string.dats
	atscc -O2 -o prelude_string prelude_string.dats

######

libc_dirent: libc_dirent.dats
	atscc -O2 -o libc_dirent libc_dirent.dats

######

libats_iterint: libats_iterint.dats
	atscc -O2 -o libats_iterint libats_iterint.dats

libats_intinf: libats_intinf.dats
	atscc -O2 -o libats_intinf libats_intinf.dats -lgmp

libats_regexp: libats_regexp.dats
	atscc -O2 -o libats_regexp libats_regexp.dats -lpcre

######

clean::
	rm -f *~
	rm -f a.out *_?ats.c *_?ats.o

cleanall: clean
	rm -f prelude_string
	rm -f libc_dirent
	rm -f libats_intinf
	rm -f libats_regexp

###### end of [Makefile] ######
