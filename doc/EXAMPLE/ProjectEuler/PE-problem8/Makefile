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
  problem8-hwxi \

######

problem8-hwxi: problem8-hwxi.dats
	$(ATSCC) -o $@ problem8-hwxi.dats && ./problem8-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem8-hwxi

###### end of [Makefile] ######
