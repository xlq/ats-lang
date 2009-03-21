######
#
# some examples in ATS involving UNIX socket programming
#
######

all: \
  daytime_tcpclient \
  daytime_tcpserver \
  echo_tcpclient \
  echo_tcpserver \

######

daytime_tcpclient: daytime_tcpclient.dats
	atscc -o daytime_tcpclient daytime_tcpclient.dats

daytime_tcpserver: daytime_tcpserver.dats
	atscc -o daytime_tcpserver daytime_tcpserver.dats

######

echo_tcpclient: echo_tcpclient.dats
	atscc -o echo_tcpclient echo_tcpclient.dats

echo_tcpserver: echo_tcpserver.dats
	atscc -o echo_tcpserver echo_tcpserver.dats

######

html::
	atsopt --posmark_html -d daytime_tcpclient.dats > daytime_tcpclient_dats.html
	atsopt --posmark_html -d daytime_tcpserver.dats > daytime_tcpserver_dats.html
	atsopt --posmark_html -d echo_tcpserver.dats > echo_tcpclient_dats.html
	atsopt --posmark_html -d echo_tcpserver.dats > echo_tcpserver_dats.html

######

clean::
	rm -f a.out *_dats.c *_dats.o *~

cleanall: clean
	rm -f daytime_tcpserver
	rm -f daytime_tcpclient
	rm -f echo_tcpserver
	rm -f echo_tcpclient

###### end of [Makefile] ######
