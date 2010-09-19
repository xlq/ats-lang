######
#
# A simple Makefile
#
######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(or $(ATSHOMEQ), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem20-hwxi \
  problem20-hwxi2 \

######

ATS_PROOFCHECK=-D_ATS_PROOFCHECK
ATS_PROOFCHECK=

######

problem20-hwxi: problem20-hwxi.dats
	$(ATSCC) -o $@ problem20-hwxi.dats -lats -lgmp && ./problem20-hwxi
problem20-hwxi2: problem20-hwxi2.dats
	$(ATSCC) $(ATS_PROOFCHECK) -o $@ problem20-hwxi2.dats -lats -lgmp && ./problem20-hwxi2

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem20-hwxi
	rm -f problem20-hwxi2

###### end of [Makefile] ######
