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
  problem15-hwxi \
  problem15-mberndt \
  problem15-hwxi2 \

######

problem15-hwxi: problem15-hwxi.dats
	$(ATSCC) -o $@ problem15-hwxi.dats -lats -lgmp && ./problem15-hwxi

problem15-mberndt: problem15-mberndt.dats
	$(ATSCC) -D_ATS_PROOFCHECK -o $@ problem15-mberndt.dats && ./problem15-mberndt

problem15-hwxi2: problem15-hwxi2.dats
	$(ATSCC) -o $@ problem15-hwxi2.dats && ./problem15-hwxi2

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem15-hwxi
	rm -f problem15-mberndt
	rm -f problem15-hwxi2

###### end of [Makefile] ######
