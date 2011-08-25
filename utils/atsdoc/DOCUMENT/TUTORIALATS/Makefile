#
#
# A Simple Makefile
#
#

######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSDOC=$(ATSHOMEQ)/bin/atsdoc
#LIBATSDOC=$(ATSHOMEQ)/libatsdoc

######

all: html uploadloc

######

cleanall::

######

DBSRC := \
  main.db \
  preface.db \
  chap_syncolor_atxt.db \
  chap_filename_atxt.db \
  chap_fileincl_atxt.db \
  chap_fixity_atxt.db \
  chap_mainats_atxt.db \
  chap_tailrec_atxt.db \
  chap_mutailrec_atxt.db \
  chap_hofun_atxt.db \
  chap_funlist_atxt.db \
  chap_reference_atxt.db \
  chap_callbyref_atxt.db \
  chap_lazyeval_atxt.db \
  chap_stkalloc_atxt.db \

######

html:: $(DBSRC)
	jw -b html --output HTML/ main.db
cleanall:: ; $(RMF) HTML/*.html

pdf: $(DBSRC)
	jw -b pdf --output PDF/ main.db
cleanall:: ; $(RMF) PDF/main.pdf

######

chap_syncolor: chap_syncolor_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_syncolor_atxt.dats: chap_syncolor.atxt
	$(ATSDOC) -do $@ -i $< > chap_syncolor_atxt.txt
chap_syncolor_atxt.db: chap_syncolor ; ./$< > $@

clean:: ; $(RMF) chap_syncolor 
cleanall:: ; $(RMF) chap_syncolor_atxt.db

######

chap_filename: chap_filename_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_filename_atxt.dats: chap_filename.atxt
	$(ATSDOC) -do $@ -i $< > chap_filename_atxt.txt
chap_filename_atxt.db: chap_filename ; ./$< > $@

clean:: ; $(RMF) chap_filename 
cleanall:: ; $(RMF) chap_filename_atxt.db

######

chap_fileincl: chap_fileincl_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_fileincl_atxt.dats: chap_fileincl.atxt
	$(ATSDOC) -do $@ -i $< > chap_fileincl_atxt.txt
chap_fileincl_atxt.db: chap_fileincl ; ./$< > $@

clean:: ; $(RMF) chap_fileincl 
cleanall:: ; $(RMF) chap_fileincl_atxt.db

######

chap_fixity: chap_fixity_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_fixity_atxt.dats: chap_fixity.atxt
	$(ATSDOC) -do $@ -i $< > chap_fixity_atxt.txt
chap_fixity_atxt.db: chap_fixity ; ./$< > $@

clean:: ; $(RMF) chap_fixity 
cleanall:: ; $(RMF) chap_fixity_atxt.db

######

chap_mainats: chap_mainats_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_mainats_atxt.dats: chap_mainats.atxt
	$(ATSDOC) -do $@ -i $< > chap_mainats_atxt.txt
chap_mainats_atxt.db: chap_mainats ; ./$< > $@

clean:: ; $(RMF) chap_mainats 
cleanall:: ; $(RMF) chap_mainats_atxt.db

######

chap_tailrec: chap_tailrec_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_tailrec_atxt.dats: chap_tailrec.atxt
	$(ATSDOC) -do $@ -i $< > chap_tailrec_atxt.txt
chap_tailrec_atxt.db: chap_tailrec ; ./$< > $@

clean:: ; $(RMF) chap_tailrec 
cleanall:: ; $(RMF) chap_tailrec_atxt.db

######

chap_mutailrec: chap_mutailrec_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_mutailrec_atxt.dats: chap_mutailrec.atxt
	$(ATSDOC) -do $@ -i $< > chap_mutailrec_atxt.txt
chap_mutailrec_atxt.db: chap_mutailrec ; ./$< > $@

clean:: ; $(RMF) chap_mutailrec 
cleanall:: ; $(RMF) chap_mutailrec_atxt.db

######

chap_hofun: chap_hofun_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_hofun_atxt.dats: chap_hofun.atxt
	$(ATSDOC) -do $@ -i $< > chap_hofun_atxt.txt
chap_hofun_atxt.db: chap_hofun ; ./$< > $@

clean:: ; $(RMF) chap_hofun 
cleanall:: ; $(RMF) chap_hofun_atxt.db

######

chap_funlist: chap_funlist_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_funlist_atxt.dats: chap_funlist.atxt
	$(ATSDOC) -do $@ -i $< > chap_funlist_atxt.txt
chap_funlist_atxt.db: chap_funlist ; ./$< > $@

clean:: ; $(RMF) chap_funlist 
cleanall:: ; $(RMF) chap_funlist_atxt.db

######

chap_reference: chap_reference_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_reference_atxt.dats: chap_reference.atxt
	$(ATSDOC) -do $@ -i $< > chap_reference_atxt.txt
chap_reference_atxt.db: chap_reference ; ./$< > $@

clean:: ; $(RMF) chap_reference 
cleanall:: ; $(RMF) chap_reference_atxt.db

######

chap_callbyref: chap_callbyref_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_callbyref_atxt.dats: chap_callbyref.atxt
	$(ATSDOC) -do $@ -i $< > chap_callbyref_atxt.txt
chap_callbyref_atxt.db: chap_callbyref ; ./$< > $@

clean:: ; $(RMF) chap_callbyref 
cleanall:: ; $(RMF) chap_callbyref_atxt.db

######

chap_lazyeval: chap_lazyeval_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_lazyeval_atxt.dats: chap_lazyeval.atxt
	$(ATSDOC) -do $@ -i $< > chap_lazyeval_atxt.txt
chap_lazyeval_atxt.db: chap_lazyeval ; ./$< > $@

clean:: ; $(RMF) chap_lazyeval 
cleanall:: ; $(RMF) chap_lazyeval_atxt.db

######

chap_stkalloc: chap_stkalloc_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_stkalloc_atxt.dats: chap_stkalloc.atxt
	$(ATSDOC) -do $@ -i $< > chap_stkalloc_atxt.txt
chap_stkalloc_atxt.db: chap_stkalloc ; ./chap_stkalloc > $@

clean:: ; $(RMF) chap_stkalloc 
cleanall:: ; $(RMF) chap_stkalloc_atxt.db

######

upload:
	scp -r HTML ats-hwxi,ats-lang@web.sourceforge.net:htdocs/DOCUMENT/TUTORIALATS

uploadloc:
	cp -rf HTML $(HOME)/public_html/ATS/DOCUMENT/TUTORIALATS
	chmod 644 $(HOME)/public_html/ATS/DOCUMENT/TUTORIALATS/HTML/*.html

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
	$(RMF) *_atxt.txt *_atxt.dats

cleanall:: clean

###### end of [Makefile] ######
