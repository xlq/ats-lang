#
#
# Some programs involving OpenGL ES 2.0
#
# Author: Artyom Shalkhakov (artyom DOT shalkhakov AT gmail DOT com)
# Time: May, 2011
#

######

ATSUSRQ="$(ATSHOME)"
ATSLIBQ="$(ATSHOME)"
ifeq ("$(ATSHOME)","")
ATSUSRQ="/usr"
ATSLIBQ="/usr/lib/ats-anairiats-0.2.4"
endif

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSLEX=$(ATSUSRQ)/bin/atslex
ATSMISCCTRB=$(ATSHOME)/contrib/GLES2/atsctrb_GLES2.o

######

.PHONY:: all
all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean

######

checkall:: test01 test02 test03
cleanall:: ; $(RMF) test01 test02 test03

util.o: util_sats.o util_dats.o
	ld -r -o $@ util_sats.o util_dats.o

util_sats.o: SATS/util.sats
	$(ATSCC) -IATS $(HOME) -I $(HOME) -o $@ -c SATS/util.sats
util_dats.o: DATS/util.dats
	$(ATSCC) -IATS $(HOME) -I $(HOME) -o $@ -c DATS/util.dats

obj_sats.o: SATS/obj.sats
	$(ATSCC) -IATS $(HOME) -I $(HOME) \
	  -o $@ -c SATS/obj.sats
######

obj_lats.dats: DATS/obj.lats
	$(ATSLEX) < $< > $@
obj_lats_dats.o: obj_lats.dats obj_sats.o
	$(ATSCC) -IATS $(HOME) -I $(HOME) \
	  -o $@ -c obj_lats.dats obj_sats.o

######

mat4.o: mat4_sats.o mat4_dats.o
	ld -r -o $@ mat4_sats.o mat4_dats.o

mat4_sats.o: utils/mat4.sats
	$(ATSCC) -IATS $(UTILS) -I $(UTILS) -o $@ -c $<
mat4_dats.o: DATS/mat4.dats
	$(ATSCC) -IATS $(UTILS) -I $(UTILS) -o $@ -c $<

######

test01: GLES2-test01.dats util.o
	$(ATSCC) -IATS $(HOME) -I $(HOME) \
	  -o test01 GLES2-test02.dats util.o \
	  $(ATSMISCCTRB) -lm -lX11 -lEGL -lGLESv2

######

test02: GLES2-test02.dats util.o
	$(ATSCC) -IATS $(HOME) -I $(HOME) \
	  -o test02 GLES2-test02.dats util.o \
	  $(ATSMISCCTRB) -lm -lX11 -lEGL -lGLESv2

######

test03: GLES2-test03.dats util.o obj_lats_dats.o mat4.o
	$(ATSCC) -IATS $(HOME) -I $(HOME) \
	  -o test03 GLES2-test03.dats \
	   prelude/DATS/list_vt.dats libats/DATS/rarray.dats libats/SATS/rarray.sats libc/SATS/stdlib.sats libc/SATS/fcntl.sats \
	   libc/sys/SATS/types.sats \
	   libats/lex/lexing.dats libats/lex/lexing.sats libats/lex/tables.dats \
	   prelude/DATS/reference.dats \
	  $(ATSMISCCTRB) util.o obj_lats_dats.o mat4.o \
	  -lX11 -lEGL -lGLESv2 -lats_lex

#######

RMF = rm -f

#######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
	$(RMF) *.o
	$(RMF) obj_lats.dats

###### end of [Makefile] #######
