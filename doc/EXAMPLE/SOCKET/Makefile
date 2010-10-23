######
#
# some examples in ATS involving UNIX socket programming
#
######

ATSHOMEQ=$(or "$(ATSHOME)", "/usr")
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

.PHONY: all
all: checkall

######

checkall: compall cleanall

######

compall: \
  daytime_tcpclient \
  daytime_tcpserver \
  echo_tcpclient \
  echo_tcpserver \
  echo_preforking \

######

daytime_tcpclient: daytime_tcpclient.dats
	$(ATSCC) -o daytime_tcpclient daytime_tcpclient.dats

daytime_tcpserver: daytime_tcpserver.dats
	$(ATSCC) -o daytime_tcpserver daytime_tcpserver.dats

######

echo_tcpclient: echo_tcpclient.dats
	$(ATSCC) -o echo_tcpclient echo_tcpclient.dats

echo_tcpserver: echo_tcpserver.dats
	$(ATSCC) -o echo_tcpserver echo_tcpserver.dats

######

echo_preforking: echo_preforking.dats
	$(ATSCC) -o echo_preforking echo_preforking.dats

######

html::
	$(ATSOPT) --posmark_html -d daytime_tcpclient.dats > daytime_tcpclient_dats.html
	$(ATSOPT) --posmark_html -d daytime_tcpserver.dats > daytime_tcpserver_dats.html
	$(ATSOPT) --posmark_html -d echo_tcpserver.dats > echo_tcpclient_dats.html
	$(ATSOPT) --posmark_html -d echo_tcpserver.dats > echo_tcpserver_dats.html
	$(ATSOPT) --posmark_html -d echo_preforking.dats > echo_preforking_dats.html

######

xref::
	$(ATSOPT) --posmark_xref=XREF -d \
          $(ATSHOME)/utils/xref/ats_prelude_xref.dats > /dev/null
	$(ATSOPT) --posmark_xref=XREF -d daytime_tcpclient.dats > daytime_tcpclient_dats.html
	$(ATSOPT) --posmark_xref=XREF -d daytime_tcpserver.dats > daytime_tcpserver_dats.html
	$(ATSOPT) --posmark_xref=XREF -d echo_tcpserver.dats > echo_tcpclient_dats.html
	$(ATSOPT) --posmark_xref=XREF -d echo_tcpserver.dats > echo_tcpserver_dats.html
	$(ATSOPT) --posmark_xref=XREF -d echo_preforking.dats > echo_preforking_dats.html

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_dats.c *_dats.o
	$(RMF) ./SOCKET/*

cleanall:: clean
	$(RMF) *_?ats.html
	$(RMF) XREF/*_?ats.html
	$(RMF) daytime_tcpserver
	$(RMF) daytime_tcpclient
	$(RMF) echo_tcpserver
	$(RMF) echo_tcpclient
	$(RMF) echo_preforking

###### end of [Makefile] ######
