AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libsmtutil.la

libsmtutil_la_SOURCES = \
	Makefile.am \
	Makefile.in \
	command.cpp \
	command.h


EXTRA_DIST = \
	command.i

