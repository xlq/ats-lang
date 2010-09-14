#
#
# Makefile for some examples in ATS/LF
#
#

######

ATSHOMEQ=$(or "$(ATSHOME)", "/usr")
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

DIR=/home/fac2/hwxi/public_html/ATS/EXAMPLE/LF

######

all:: \
#  ATS \

all:: \
#  CallByValue \

all:: \
  ClosureConv \
  CPS \

all:: \
#  CutElimIL \

all:: \
  CutElimILL \
  HilbertCalculus \
  infprime \
  irrationality-of-sqrt2 \
  ITPT \
  KolmogorovTrans \

all:: \
#  mini-ML \
 
all:: \
  naive-set.dats \
  pigeonhole \
  PyTri \
  STLC-foas \

all:: \
#  STLC-hoas \

all:: \
  STLC-SN-foas \
  STLC-SN-hoas \

######

ATSCCFLAG=--typecheck

ATS: ; $(ATSCC) $(ATSCCFLAG) ATS.dats
BinaryTree: ; $(ATSCC) $(ATSCCFLAG) BinaryTree.dats
CallByValue: ; $(ATSCC) $(ATSCCFLAG) CallByValue.dats
ClosureConv: ; $(ATSCC) $(ATSCCFLAG) ClosureConv.dats
CPS: ; $(ATSCC) $(ATSCCFLAG) CPS.dats
CutElimIL: ; $(ATSCC) $(ATSCCFLAG) CutElimIL.dats
CutElimILL: ; $(ATSCC) $(ATSCCFLAG) CutElimILL.dats
HilbertCalculus: ; $(ATSCC) $(ATSCCFLAG) HilbertCalculus.dats
infprime: ; $(ATSCC) $(ATSCCFLAG) infprime.dats
irrationality-of-sqrt2: ; $(ATSCC) $(ATSCCFLAG) irrationality-of-sqrt2.dats
ITPT: ; $(ATSCC) $(ATSCCFLAG) ITPT.dats
KolmogorovTrans: ; $(ATSCC) $(ATSCCFLAG) KolmogorovTrans.dats
mini-ML: ; $(ATSCC) $(ATSCCFLAG) mini-ML.dats
naive-set: ; $(ATSCC) $(ATSCCFLAG) naive-set.dats
pigeonhole: ; $(ATSCC) $(ATSCCFLAG) pigeonhole.dats
PyTri: ; $(ATSCC) $(ATSCCFLAG) PyTri.dats
STLC-foas: ; $(ATSCC) $(ATSCCFLAG) STLC-foas.dats
STLC-hoas: ; $(ATSCC) $(ATSCCFLAG) STLC-hoas.dats
STLC-SN-foas: ; $(ATSCC) $(ATSCCFLAG) STLC-SN-foas.dats
STLC-SN-hoas: ; $(ATSCC) $(ATSCCFLAG) STLC-SN-hoas.dats

######

POSMARK=--posmark_html

posmark::
#	$(ATSOPT) $(POSMARK) -d ATS.dats
	$(ATSOPT) $(POSMARK) -d BinaryTree.dats > BinaryTree_dats.html
#	$(ATSOPT) $(POSMARK) -d CallByValue.dats > CallByValue_dats.html
	$(ATSOPT) $(POSMARK) -d ClosureConv.dats > ClosureConv_dats.html
	$(ATSOPT) $(POSMARK) -d CPS.dats > CPS_dats.html
#	$(ATSOPT) $(POSMARK) -d CutElimIL.dats > CutElimIL_dats.html
	$(ATSOPT) $(POSMARK) -d CutElimILL.dats > CutElimILL_dats.html
	$(ATSOPT) $(POSMARK) -d HilbertCalculus.dats > HilbertCalculus_dats.html
	$(ATSOPT) $(POSMARK) -d infprime.dats > infprime_dats.html
	$(ATSOPT) $(POSMARK) -d irrationality-of-sqrt2.dats > irrationality-of-sqrt2_dats.html
	$(ATSOPT) $(POSMARK) -d ITPT.dats > ITPT_dats.html
	$(ATSOPT) $(POSMARK) -d KolmogorovTrans.dats > KolmogorovTrans_dats.html
	$(ATSOPT) $(POSMARK) -d mini-ML.dats > mini-ML_dats.html
	$(ATSOPT) $(POSMARK) -d naive-set.dats > naive-set_dats.html
	$(ATSOPT) $(POSMARK) -d pigeonhole.dats > pigeonhole_dats.html
	$(ATSOPT) $(POSMARK) -d PyTri.dats > PyTri_dats.html
	$(ATSOPT) $(POSMARK) -d STLC-foas.dats > STLC-foas_dats.html
#	$(ATSOPT) $(POSMARK) -d STLC-hoas.dats > STLC-hoas_dats.html
	$(ATSOPT) $(POSMARK) -d STLC-SN-foas.dats > STLC-SN-foas_dats.html
	$(ATSOPT) $(POSMARK) -d STLC-SN-hoas.dats > STLC-SN-hoas_dats.html

######

update::
	cp Makefile $(DIR)
	cp ATS.dats $(DIR)
	cp BinaryTree.dats $(DIR)
	cp ClosureConv.dats $(DIR)
	cp CPS.dats $(DIR)
	cp CutElimIL.dats $(DIR)
	cp CutElimILL.dats $(DIR)
	cp HilbertCalculus.dats $(DIR)
	cp infprime.dats $(DIR)
	cp irrationality-of-sqrt2.dats $(DIR)
	cp ITPT.dats $(DIR)
	cp KolmogorovTrans.dats $(DIR)
	cp mini-ML.dats $(DIR)
	cp naive-set.dats $(DIR)
	cp pigeonhole.dats $(DIR)
	cp PyTri.dats $(DIR)
	cp STLC-foas.dats $(DIR)
	cp STLC-hoas.dats $(DIR)
	cp STLC-SN-foas.dats $(DIR)
	cp STLC-SN-hoas.dats $(DIR)

######

clean::
	rm -f *_dats.c *_sats.c *~

cleanall: clean
	rm -f *_?ats.html

###### end of [Makefile] ######
