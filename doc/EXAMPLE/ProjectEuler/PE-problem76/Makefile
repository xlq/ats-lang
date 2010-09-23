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
  problem76-hwxi \

######

problem76-hwxi: problem76-hwxi.dats
	$(ATSCC) -O2 -o $@ problem76-hwxi.dats && ./problem76-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem76-hwxi

###### end of [Makefile] ######
