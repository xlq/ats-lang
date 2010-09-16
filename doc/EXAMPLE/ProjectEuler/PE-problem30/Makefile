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
  problem30-hwxi \

######

problem30-hwxi: problem30-hwxi.dats
	$(ATSCC) -O3 -o $@ problem30-hwxi.dats && ./problem30-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem30-hwxi

###### end of [Makefile] ######
