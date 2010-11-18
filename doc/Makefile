######
#
# A simple Makefile for updating various ATS docs
#
######

all:: \
  ATS \
  TUTORIAL \
  EXAMPLE EXAMPLES_new \
  IMPLEMENTATION \
  RESOURCE \
  LIBRARY \
  PAPER \
  CHANGELOG

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

atsgrammar_desc::
	scp DOCUMENTATION/ATS_GRAMMAR/atsgrammar_desc.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/DOCUMENTATION/atsgrammar_desc.html

atsgrammar_yats::
	scp DOCUMENTATION/ATS_GRAMMAR/atsgrammar_yats.html \
          ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/DOCUMENTATION/atsgrammar_yats.html

###### end of [Makefile] ######
