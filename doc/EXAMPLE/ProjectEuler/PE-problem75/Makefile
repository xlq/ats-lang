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
  problem75-hwxi \

######

problem75-hwxi: problem75-hwxi.dats
	$(ATSCC) -O2 -o $@ problem75-hwxi.dats -lm && ./problem75-hwxi

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f problem75-hwxi

###### end of [Makefile] ######
