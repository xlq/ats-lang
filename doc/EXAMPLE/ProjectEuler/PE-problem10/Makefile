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
  problem10-hwxi \

######

problem10-hwxi: problem10-hwxi.dats
	$(ATSCC) -O2 -o $@ problem10-hwxi.dats && ./problem10-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem10-hwxi

###### end of [Makefile] ######
