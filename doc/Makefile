######
#
# A simple Makefile for updating various ATS docs
#
######

all:: ATS
all:: TUTORIAL
all:: EXAMPLE
all:: EXAMPLES_new
all:: IMPLEMENTATION
all:: RESOURCE
all:: LIBRARY
all:: PAPER
all:: CHANGELOG

######

ATS::
	scp ATS.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/ATS.html

FAQ::
	scp FAQ.txt \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/FAQ.txt

TUTORIAL::
	scp TUTORIAL/tutorial.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/TUTORIAL/tutorial.html

EXAMPLE::
	scp EXAMPLE/example.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/EXAMPLE/example.html

EXAMPLE_new::
	scp EXAMPLE/example_new.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/EXAMPLE/example_new.html

IMPLEMENTATION::
	scp IMPLEMENTATION/implementation.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/IMPLEMENTATION/implementation.html

IMPLEMENTATION/ATSOPT::
	scp -r IMPLEMENTATION/ATSOPT \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/IMPLEMENTATION

RESOURCE::
	scp RESOURCE/resource.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/RESOURCE/resource.html

LIBRARY::
	scp LIBRARY/library.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/LIBRARY/library.html

PAPER::
	scp PAPER/paper.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/PAPER/paper.html

CHANGELOG::
	scp CHANGELOG/changelog.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/CHANGELOG/changelog.html

######

sysprog::
	scp BOOK/sysprog.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/DOCUMENTATION/sysprog.html

atsgrammar::
	scp \
          DOCUMENTATION/ATS_GRAMMAR/ats_grammar_desc.html \
          DOCUMENTATION/ATS_GRAMMAR/ats_grammar_yats.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/DOCUMENTATION/GRAMMAR/

###### end of [Makefile] ######
