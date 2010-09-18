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
  problem49-hwxi \

######

problem49-hwxi: problem49-hwxi.dats
	$(ATSCC) -O2 -o $@ problem49-hwxi.dats && ./problem49-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem49-hwxi

###### end of [Makefile] ######
