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

update:
	atsopt --posmark_html_only -d daytime_tcpclient.dats
	atsopt --posmark_html_only -d daytime_tcpserver.dats
	atsopt --posmark_html_only -d echo_tcpclient.dats
	atsopt --posmark_html_only -d echo_tcpserver.dats

######

clean::
	rm -f a.out *_dats.c *_dats.o *~

cleanall: clean
	rm -f daytime_tcpserver
	rm -f daytime_tcpclient
	rm -f echo_tcpserver
	rm -f echo_tcpclient

###### end of [Makefile] ######
