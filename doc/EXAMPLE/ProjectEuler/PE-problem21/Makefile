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
  problem21-hwxi \

######

problem21-hwxi: problem21-hwxi.dats
	$(ATSCC) -o $@ problem21-hwxi.dats && ./problem21-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem21-hwxi

###### end of [Makefile] ######
