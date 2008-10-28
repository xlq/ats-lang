#
#
# A simple (single threaded) HTTP server implemented in ATS
#
#

ATSCC="$(ATSHOME)"/bin/atscc

#
# If on SunOS, please add [-lsocket]
#

server: server.dats
	$(ATSCC) -D_ATS_GCATS -o server -O3 server.dats

######

DIR=/home/fac2/hwxi/public_html/ATS/EXAMPLE/HttpServer

update::
	cp Makefile $(DIR)
	cp server.dats $(DIR)

######

clean::
	rm -f *_dats.c *_sats.c *~

cleanall:: clean
	rm -f server

###### end of [Makefile] ######
