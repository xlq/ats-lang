#
# A simple Makefile for building modules
#

######

KVERS = $(shell uname -r)

######

# Kernel modules
obj-m += hello_mod_dats.o

#
# Specify flags for the module compilation.
#
EXTRA_CFLAGS = \
  -I$(ATSHOME) \
  -D_ATS_HEADER_NONE -D_ATS_PRELUDE_NONE \
  -g

######

build: kernel_modules

######

kernel_modules:
	make -C /lib/modules/$(KVERS)/build M=$(CURDIR) modules

######

clean:
	make -C /lib/modules/$(KVERS)/build M=$(CURDIR) clean

###### end of [Makefile] ######
