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
  problem52-hwxi \

######

problem52-hwxi: problem52-hwxi.dats
	$(ATSCC) -o $@ problem52-hwxi.dats && ./problem52-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem52-hwxi

###### end of [Makefile] ######
