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
  problem301-hwxi \

######

problem301-hwxi: problem301-hwxi.dats
	$(ATSCC) -O3 -o $@ problem301-hwxi.dats && ./problem301-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem301-hwxi

###### end of [Makefile] ######
