AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/../.. -I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = lib$dir.la

lib$dir_la_SOURCES = \
	theory_$dir.h \
	theory_$dir.cpp \
	theory_$dir_rewriter.h \
	theory_$dir_type_rules.h

EXTRA_DIST = \
	kinds \
	options_handlers.h
