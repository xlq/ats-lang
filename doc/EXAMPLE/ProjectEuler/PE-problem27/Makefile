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
  problem27-hwxi \

######

problem27-hwxi: problem27-hwxi.dats
	$(ATSCC) -O2 -o $@ problem27-hwxi.dats && ./problem27-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem27-hwxi

###### end of [Makefile] ######
