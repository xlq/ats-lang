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
  problem53-hwxi \

######

problem53-hwxi: problem53-hwxi.dats
	$(ATSCC) -o $@ problem53-hwxi.dats && ./problem53-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem53-hwxi

###### end of [Makefile] ######
