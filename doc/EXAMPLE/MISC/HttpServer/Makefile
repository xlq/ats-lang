#
#
# A simple (single threaded) HTTP server implemented in ATS
#
#

######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

.PHONY: all
all:: checkall

checkall: compall cleanall
compall:: server server2

######

#
# If on SunOS, please add [-lsocket]
#

server: server.dats
	$(ATSCC) -D_ATS_GCATS -o server -O2 server.dats

server2: server2.dats
	$(ATSCC) -D_ATS_GCATS -o server2 -O2 server2.dats

######

DIR=/home/fac2/hwxi/public_html/ATS/EXAMPLE/HttpServer

update::
	cp Makefile $(DIR)
	cp server.dats $(DIR)

######

clean::
	rm -f *_dats.c *_sats.c *~

cleanall:: clean
	rm -f server server2

###### end of [Makefile] ######
