#
#
# A simple (single threaded) HTTP server implemented in ATS
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
all:: checkall cleanall

checkall::
cleanall:: clean

######

#
# If on SunOS, please add [-lsocket]
#

checkall:: server
server: server.dats
	$(ATSCC) -D_ATS_GCATS -o server -O2 server.dats
cleanall:: ; rm -f server

checkall:: server2
server2: server2.dats
	$(ATSCC) -D_ATS_GCATS -o server2 -O2 server2.dats
cleanall:: ; rm -f server2

######

DIR=/home/fac2/hwxi/public_html/ATS/EXAMPLE/HttpServer

update::
	cp Makefile $(DIR)
	cp server.dats $(DIR)

######

clean::
	rm -f *~
	rm -f *_dats.c *_sats.c

###### end of [Makefile] ######
