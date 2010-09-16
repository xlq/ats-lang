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
  problem35-hwxi \

######

problem35-hwxi: problem35-hwxi.dats
	$(ATSCC) -O3 -o $@ problem35-hwxi.dats && ./problem35-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem35-hwxi

###### end of [Makefile] ######
