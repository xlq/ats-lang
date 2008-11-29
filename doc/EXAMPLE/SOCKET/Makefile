######
#
# some examples involving UNIX socket programming
#
######

daytimetcpclient: daytimetcpclient.dats
	atscc -o daytimetcpclient daytimetcpclient.dats

daytimetcpserver: daytimetcpserver.dats
	atscc -o daytimetcpserver daytimetcpserver.dats

######

clean::
	rm -f a.out *_dats.c *_dats.o *~

cleanall: clean
	rm -f daytimetcpserver
	rm -f daytimetcpclient

###### end of [Makefile] ######
