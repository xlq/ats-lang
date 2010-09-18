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
  problem38-hwxi \

######

problem38-hwxi: problem38-hwxi.dats
	$(ATSCC) -O2 -o $@ problem38-hwxi.dats && ./problem38-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem38-hwxi

###### end of [Makefile] ######
