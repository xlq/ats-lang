#
#
# Some examples in ATS/LF
#
#

######

DIR=/home/fac2/hwxi/public_html/ATS/EXAMPLE/LF

######

all: ATS \
     CallByValue \
     ClosureConv \
     CPS \
     CutElimIL \
     CutElimILL \
     HilbertCalculus \
     irrationality_of_sqrt2 \
     ITPT \
     KolmogorovTrans \
     miniML \
     STLC-foas \
     STLC-hoas \
     STLC-SN-foas \
     STLC-SN-hoas \

######

ATSCC="$(ATSHOME)"/bin/atscc
ATSCCFLAG=--typecheck

######

ATS: ; $(ATSCC) $(ATSCCFLAG) ATS.dats
CallByValue: ; $(ATSCC) $(ATSCCFLAG) CallByValue.dats
ClosureConv: ; $(ATSCC) $(ATSCCFLAG) ClosureConv.dats
CPS: ; $(ATSCC) $(ATSCCFLAG) CPS.dats
CutElimIL: ; $(ATSCC) $(ATSCCFLAG) CutElimIL.dats
CutElimILL: ; $(ATSCC) $(ATSCCFLAG) CutElimILL.dats
HilbertCalculus: ; $(ATSCC) $(ATSCCFLAG) HilbertCalculus.dats
irrationality_of_sqrt2: ; $(ATSCC) $(ATSCCFLAG) irrationality_of_sqrt2.dats
ITPT: ; $(ATSCC) $(ATSCCFLAG) ITPT.dats
KolmogorovTrans: ; $(ATSCC) $(ATSCCFLAG) KolmogorovTrans.dats
miniML: ; $(ATSCC) $(ATSCCFLAG) miniML.dats
STLC-foas: ; $(ATSCC) $(ATSCCFLAG) STLC-foas.dats
STLC-hoas: ; $(ATSCC) $(ATSCCFLAG) STLC-hoas.dats
STLC-SN-foas: ; $(ATSCC) $(ATSCCFLAG) STLC-SN-foas.dats
STLC-SN-hoas: ; $(ATSCC) $(ATSCCFLAG) STLC-SN-hoas.dats

######

typecheck::
#	$(ATSCC) $(ATSCCFLAG) ATS.dats
#	$(ATSCC) $(ATSCCFLAG) CallByValue.dats
	$(ATSCC) $(ATSCCFLAG) ClosureConv.dats
	$(ATSCC) $(ATSCCFLAG) CPS.dats
#	$(ATSCC) $(ATSCCFLAG) CutElimIL.dats
	$(ATSCC) $(ATSCCFLAG) CutElimILL.dats
	$(ATSCC) $(ATSCCFLAG) HilbertCalculus.dats
	$(ATSCC) $(ATSCCFLAG) irrationality_of_sqrt2.dats
	$(ATSCC) $(ATSCCFLAG) ITPT.dats
	$(ATSCC) $(ATSCCFLAG) KolmogorovTrans.dats
	$(ATSCC) $(ATSCCFLAG) miniML.dats
	$(ATSCC) $(ATSCCFLAG) STLC-foas.dats
#	$(ATSCC) $(ATSCCFLAG) STLC-hoas.dats
	$(ATSCC) $(ATSCCFLAG) STLC-SN-foas.dats
	$(ATSCC) $(ATSCCFLAG) STLC-SN-hoas.dats

######

ATSOPT=$(ATSHOME)/bin/atsopt
POSMARK=--posmark_html_only

posmark::
#	$(ATSOPT) $(POSMARK) -d ATS.dats
#	$(ATSOPT) $(POSMARK) -d CallByValue.dats
	$(ATSOPT) $(POSMARK) -d ClosureConv.dats
	$(ATSOPT) $(POSMARK) -d CPS.dats
#	$(ATSOPT) $(POSMARK) -d CutElimIL.dats
	$(ATSOPT) $(POSMARK) -d CutElimILL.dats
	$(ATSOPT) $(POSMARK) -d HilbertCalculus.dats
	$(ATSOPT) $(POSMARK) -d irrationality_of_sqrt2.dats
	$(ATSOPT) $(POSMARK) -d ITPT.dats
	$(ATSOPT) $(POSMARK) -d KolmogorovTrans.dats
	$(ATSOPT) $(POSMARK) -d miniML.dats
	$(ATSOPT) $(POSMARK) -d STLC-foas.dats
#	$(ATSOPT) $(POSMARK) -d STLC-hoas.dats
	$(ATSOPT) $(POSMARK) -d STLC-SN-foas.dats
	$(ATSOPT) $(POSMARK) -d STLC-SN-hoas.dats

######

update::
	cp Makefile $(DIR)
	cp ATS.dats $(DIR)
	cp ClosureConv.dats $(DIR)
	cp CPS.dats $(DIR)
	cp CutElimIL.dats $(DIR)
	cp CutElimILL.dats $(DIR)
	cp HilbertCalculus.dats $(DIR)
	cp irrationality_of_sqrt2.dats $(DIR)
	cp ITPT.dats $(DIR)
	cp KolmogorovTrans.dats $(DIR)
	cp miniML.dats $(DIR)
	cp STLC-foas.dats $(DIR)
	cp STLC-hoas.dats $(DIR)
	cp STLC-SN-foas.dats $(DIR)
	cp STLC-SN-hoas.dats $(DIR)

######

clean::
	rm -f *_dats.c *_sats.c *~
