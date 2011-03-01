######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

######

# Comment/uncomment the following line to disable/enable debugging
#DEBUG = y

######

# Add your debugging flag (or not) to CFLAGS
ifeq ($(DEBUG),y)
  DEBFLAGS = -O -g -DSCULL_DEBUG # "-O" is needed to expand inlines
else
  DEBFLAGS = -O2
endif

######

EXTRA_CFLAGS += $(DEBFLAGS)
EXTRA_CFLAGS += -I$(LDDINC)
EXTRA_CFLAGS += -I$(ATSHOME)
EXTRA_CFLAGS += -D_ATS_HEADER_NONE -D_ATS_PRELUDE_NONE

######

ifneq ($(KERNELRELEASE),)
# call from kernel build system

scull-objs := main.o
scull-objs += scull_dats.o
scull-objs += scull_data_dats.o
scull-objs += pipe.o
scull-objs += access.o

obj-m	:= scull.o

else

KERNELDIR ?= /lib/modules/$(shell uname -r)/build
PWD       := $(shell pwd)

modules:
	$(MAKE) -C $(KERNELDIR) M=$(PWD) LDDINC=$(PWD)/../include modules

endif

######

scullats: scull_dats.c scull_data_dats.c
scull_dats.c: \
  ATS/scull.dats ATS/scull.sats ; $(ATSOPT) -IATS ATS -o $@ -d $<
scull_data_dats.c: \
  ATS/scull_data.dats ATS/scull.sats ; $(ATSOPT) -IATS ATS -o $@ -d $<

######

clean:: ; rm -f *~
clean:: ; rm -f *.o *.ko
clean:: ; rm -f *.mod.c
clean:: ; rm -f *_?ats.c

depend .depend dep:
	$(CC) $(EXTRA_CFLAGS) -M *.c > .depend


ifeq (.depend,$(wildcard .depend))
include .depend
endif
