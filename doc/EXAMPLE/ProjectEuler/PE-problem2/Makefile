######
#
# A simple Makefile
#
######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem2-hwxi \
  problem2-hwxi2 \

######

problem2-hwxi: problem2-hwxi.dats
	$(ATSCC) -o $@ problem2-hwxi.dats -lats -lgmp && ./problem2-hwxi

problem2-hwxi2: problem2-hwxi2.dats
	$(ATSCC) -o $@ problem2-hwxi2.dats -lats && ./problem2-hwxi2

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem2-hwxi
	rm -f problem2-hwxi2

###### end of [Makefile] ######
