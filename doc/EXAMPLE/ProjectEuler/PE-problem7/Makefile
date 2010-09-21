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
  problem7-hwxi \
  problem7-hwxi2 \

######

problem7-hwxi: problem7-hwxi.dats
	$(ATSCC) -O2 -o $@ problem7-hwxi.dats && ./problem7-hwxi
problem7-hwxi2: problem7-hwxi2.dats
	$(ATSCC) -O2 -o $@ problem7-hwxi2.dats -lm && ./problem7-hwxi2

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem7-hwxi
	rm -f problem7-hwxi2

###### end of [Makefile] ######
