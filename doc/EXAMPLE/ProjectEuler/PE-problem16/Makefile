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
  problem16-hwxi \
  problem16-hwxi2 \

######

problem16-hwxi: problem16-hwxi.dats
	$(ATSCC) -o $@ problem16-hwxi.dats -lats -lgmp && ./problem16-hwxi

problem16-hwxi2: problem16-hwxi2.dats
	$(ATSCC) -o $@ problem16-hwxi2.dats && ./problem16-hwxi2

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem16-hwxi
	rm -f problem16-hwxi2

###### end of [Makefile] ######
