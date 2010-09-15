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
  problem37-hwxi \

######

problem37-hwxi: problem37-hwxi.dats
	$(ATSCC) -O2 -o $@ problem37-hwxi.dats && ./problem37-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem37-hwxi

###### end of [Makefile] ######
