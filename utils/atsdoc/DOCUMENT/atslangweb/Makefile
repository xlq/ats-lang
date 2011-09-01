######
#
# A simple Makefile
#
######

ATSCC=$(ATSHOME)/bin/atscc
ATSDOC=$(ATSHOME)/bin/atsdoc

######

all:: HOME
all:: DOWNLOAD
all:: DOCUMENT
all:: LIBRARY
all:: RESOURCE
all:: EXAMPLE
all:: IMPLEMENT
all:: PAPER
all:: 
all:: clean

######

ATSWEBPAGE=$(ATSHOME)/contrib/atswebpage/atsctrb_atswebpage.o

######

atslangweb_layout.dats: atslangweb_params.hats ; touch $@

atslangweb_temp: atslangweb_temp_atxt.dats ; $(ATSCC) -o $@ $< $(ATSWEBPAGE) -latsdoc
atslangweb_temp_atxt.dats: atslangweb_layout.dats \
  atslangweb_temp.atxt ; $(ATSDOC) -do $@ -i atslangweb_temp.atxt > atslangweb_temp_atxt.txt
atslangweb_temp.html: atslangweb_temp ; ./$< > $@

clean:: ; $(RMF) atslangweb_temp
cleanall:: ; $(RMF) atslangweb_temp.html
cleanall:: ; $(RMF) styles/atslangweb_temp.css

######

XRFLAGS=`pkg-config cairo --cflags --libs`
GTKFLAGS=`pkg-config gtk+-2.0 --cflags --libs`

atslangweb_bgimages: \
  atslangweb_bgimages.dats; $(ATSCC) -o $@ $(XRFLAGS) $< -lm
clean:: ; $(RMF) atslangweb_bgimages

BGIMAGES: atslangweb_bgimages ; ./$<
cleanall:: ; $(RMF) images/theSidebar_bgimage.png
cleanall:: ; $(RMF) images/thePageBody_bgimage.png

######

atslangweb_home: atslangweb_home_atxt.dats ; $(ATSCC) -o $@ $< $(ATSWEBPAGE) -latsdoc
atslangweb_home_atxt.dats: \
  atslangweb_home.atxt ; $(ATSDOC) -do $@ -i atslangweb_home.atxt > atslangweb_home_atxt.txt
HOME: atslangweb_home atslangweb_temp.html ; ./$< > atslangweb_home.html

clean:: ; $(RMF) atslangweb_home
cleanall:: ; $(RMF) atslangweb_home.html
cleanall:: ; $(RMF) styles/atslangweb_home.css

######

atslangweb_download: atslangweb_download_atxt.dats ; $(ATSCC) -o $@ $< $(ATSWEBPAGE) -latsdoc
atslangweb_download_atxt.dats: \
  atslangweb_download.atxt ; $(ATSDOC) -do $@ -i atslangweb_download.atxt > atslangweb_download_atxt.txt
DOWNLOAD:: atslangweb_download atslangweb_temp.html ; ./$< > $@/atslangweb_download.html

clean:: ; $(RMF) atslangweb_download
cleanall:: ; $(RMF) DOWNLOAD/atslangweb_download.html
cleanall:: ; $(RMF) styles/atslangweb_download.css

######

atslangweb_document: atslangweb_document_atxt.dats ; $(ATSCC) -o $@ $< $(ATSWEBPAGE) -latsdoc
atslangweb_document_atxt.dats: \
  atslangweb_document.atxt ; $(ATSDOC) -do $@ -i atslangweb_document.atxt > atslangweb_document_atxt.txt
DOCUMENT:: atslangweb_document atslangweb_temp.html ; ./$< > $@/atslangweb_document.html

clean:: ; $(RMF) atslangweb_document
cleanall:: ; $(RMF) DOCUMENT/atslangweb_document.html
cleanall:: ; $(RMF) styles/atslangweb_document.css

######

atslangweb_library: atslangweb_library_atxt.dats ; $(ATSCC) -o $@ $< $(ATSWEBPAGE) -latsdoc
atslangweb_library_atxt.dats: \
  atslangweb_library.atxt ; $(ATSDOC) -do $@ -i atslangweb_library.atxt > atslangweb_library_atxt.txt
LIBRARY:: atslangweb_library atslangweb_temp.html ; ./$< > $@/atslangweb_library.html

clean:: ; $(RMF) atslangweb_library
cleanall:: ; $(RMF) LIBRARY/atslangweb_library.html
cleanall:: ; $(RMF) styles/atslangweb_library.css

######

atslangweb_resource: atslangweb_resource_atxt.dats ; $(ATSCC) -o $@ $< $(ATSWEBPAGE) -latsdoc
atslangweb_resource_atxt.dats: \
  atslangweb_resource.atxt ; $(ATSDOC) -do $@ -i atslangweb_resource.atxt > atslangweb_resource_atxt.txt
RESOURCE:: atslangweb_resource atslangweb_temp.html ; ./$< > $@/atslangweb_resource.html

clean:: ; $(RMF) atslangweb_resource
cleanall:: ; $(RMF) RESOURCE/atslangweb_resource.html
cleanall:: ; $(RMF) styles/atslangweb_resource.css

######

atslangweb_example: atslangweb_example_atxt.dats ; $(ATSCC) -o $@ $< $(ATSWEBPAGE) -latsdoc
atslangweb_example_atxt.dats: \
  atslangweb_example.atxt ; $(ATSDOC) -do $@ -i atslangweb_example.atxt > atslangweb_example_atxt.txt
EXAMPLE:: atslangweb_example atslangweb_temp.html ; ./$< > $@/atslangweb_example.html

clean:: ; $(RMF) atslangweb_example
cleanall:: ; $(RMF) EXAMPLE/atslangweb_example.html
cleanall:: ; $(RMF) styles/atslangweb_example.css

######

atslangweb_implement: atslangweb_implement_atxt.dats ; $(ATSCC) -o $@ $< $(ATSWEBPAGE) -latsdoc
atslangweb_implement_atxt.dats: \
  atslangweb_implement.atxt ; $(ATSDOC) -do $@ -i atslangweb_implement.atxt > atslangweb_implement_atxt.txt
IMPLEMENT:: atslangweb_implement atslangweb_temp.html ; ./$< > $@/atslangweb_implement.html

clean:: ; $(RMF) atslangweb_implement
cleanall:: ; $(RMF) IMPLEMENT/atslangweb_implement.html
cleanall:: ; $(RMF) styles/atslangweb_implement.css

######

atslangweb_paper: atslangweb_paper_atxt.dats ; $(ATSCC) -o $@ $< $(ATSWEBPAGE) -latsdoc
atslangweb_paper_atxt.dats: \
  atslangweb_paper.atxt ; $(ATSDOC) -do $@ -i atslangweb_paper.atxt > atslangweb_paper_atxt.txt
PAPER:: atslangweb_paper atslangweb_temp.html ; ./$< > $@/atslangweb_paper.html

clean:: ; $(RMF) atslangweb_paper
cleanall:: ; $(RMF) PAPER/atslangweb_paper.html
cleanall:: ; $(RMF) styles/atslangweb_paper.css

######

upload:: upload_home
upload_home:: ; scp atslangweb_home.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/

upload:: upload_download
upload_download:: ; scp DOWNLOAD/atslangweb_download.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/DOWNLOAD

upload:: upload_document
upload_document:: ; scp DOCUMENT/atslangweb_document.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/DOCUMENT

upload:: upload_library
upload_library:: ; scp LIBRARY/atslangweb_library.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/LIBRARY

upload:: upload_resource
upload_resource:: ; scp RESOURCE/atslangweb_resource.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/RESOURCE

upload:: upload_example
upload_example:: ; scp EXAMPLE/atslangweb_example.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/EXAMPLE

upload:: upload_implement
upload_implement:: ; scp IMPLEMENT/atslangweb_implement.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/IMPLEMENT

upload:: upload_paper
upload_paper:: ; scp PAPER/atslangweb_paper.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/PAPER

upload:: upload_styles
upload_styles: ; scp -r styles/*.css \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/styles
upload:: upload_images
upload_images: ; scp -r images/*.png \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/images

#####################################################################
# upload_html: ; scp \						    #
#   atslangweb_home.html \					    #
#   DOWNLOAD/atslangweb_download.html \				    #
#   DOCUMENT/atslangweb_document.html \				    #
#   LIBRARY/atslangweb_library.html \				    #
#   RESOURCE/atslangweb_resource.html \				    #
#   EXAMPLE/atslangweb_example.html \				    #
#   IMPLEMENT/atslangweb_implement.html \			    #
#   PAPER/atslangweb_paper.html \				    #
#   ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/ #
#####################################################################

######

CPF=cp -f
RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.o *_?ats.c
clean:: ; $(RMF) *_atxt.txt
clean:: ; $(RMF) *_atxt.dats

cleanall:: clean

######
