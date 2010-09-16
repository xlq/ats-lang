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
  problem19-hwxi \

######

problem19-hwxi: problem19-hwxi.dats
	$(ATSCC) -o $@ problem19-hwxi.dats && ./problem19-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem19-hwxi

###### end of [Makefile] ######
