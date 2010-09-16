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
  problem17-hwxi \

######

problem17-hwxi: problem17-hwxi.dats
	$(ATSCC) -o $@ problem17-hwxi.dats && ./problem17-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem17-hwxi

###### end of [Makefile] ######
