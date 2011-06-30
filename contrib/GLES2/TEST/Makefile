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

######

UTILS="./utils"

######

util.o: util_sats.o util_dats.o
	ld -r -o $@ util_sats.o util_dats.o
util_sats.o: utils/util.sats
	$(ATSCC) -IATS $(UTILS) -I $(UTILS) -o $@ -c $<
util_dats.o: utils/util.dats
	$(ATSCC) -IATS $(UTILS) -I $(UTILS) -o $@ -c $<

######

obj_sats.o: utils/obj.sats
	$(ATSCC) -IATS $(UTILS) -I $(UTILS) -o $@ -c $<
obj_lats.dats: utils/obj.lats ; $(ATSLEX) < $< > $@
obj_lats_dats.o: obj_lats.dats
	$(ATSCC) -IATS $(UTILS) -I $(UTILS) -o $@ -c $<

######

mat4.o: mat4_sats.o mat4_dats.o
	ld -r -o $@ mat4_sats.o mat4_dats.o
mat4_sats.o: utils/mat4.sats
	$(ATSCC) -IATS $(UTILS) -I $(UTILS) -o $@ -c $<
mat4_dats.o: utils/mat4.dats
	$(ATSCC) -IATS $(UTILS) -I $(UTILS) -o $@ -c $<

######

test01: GLES2-test01.dats util.o
	$(ATSCC) $< -o $@ util.o $(ATSMISCCTRB) -lm -lX11 -lEGL -lGLESv2

######

test02: GLES2-test02.dats util.o
	$(ATSCC) $< -o $@ util.o $(ATSMISCCTRB) -lm -lX11 -lEGL -lGLESv2

######

test03: GLES2-test03.dats \
          obj_sats.o obj_lats_dats.o mat4.o util.o
	$(ATSCC) $< -o $@ \
          obj_sats.o obj_lats_dats.o mat4.o util.o \
	  $(ATSMISCCTRB) -lX11 -lEGL -lGLESv2 -lats_lex

#######

RMF = rm -f

#######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
	$(RMF) *.o
	$(RMF) obj_lats.dats

###### end of [Makefile] #######
