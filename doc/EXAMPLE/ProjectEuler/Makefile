######

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc

######

checkall: compall cleanall
compall:: \
  problem1 \
  problem2 \
  problem3 \
  problem7 \
  problem20 \
  problem25 \
  problem56 \
  problem63 \

######

problem1::; make -C PE-problem1 compall
problem2::; make -C PE-problem2 compall
problem3::; make -C PE-problem3 compall
problem7::; make -C PE-problem7 compall
problem20::; make -C PE-problem20 compall
problem25::; make -C PE-problem25 compall
problem56::; make -C PE-problem56 compall
problem63::; make -C PE-problem63 compall

######

cleanall::
	make -C PE-problem1 cleanall
	make -C PE-problem2 cleanall
	make -C PE-problem3 cleanall
	make -C PE-problem7 cleanall
	make -C PE-problem20 cleanall
	make -C PE-problem25 cleanall
	make -C PE-problem56 cleanall
	make -C PE-problem63 cleanall

###### end of [Makefile] ######
