AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libbase.la

# Do not list built sources (like integer.h, rational.h, and tls.h) here!
# Rather, list them under BUILT_SOURCES, and their .in versions under
# EXTRA_DIST.  Otherwise, they're packaged up in the tarball, which is
# no good---they belong in the configured builds/ directory.  If they
# end up in the source directory, they build the cvc4 that was
# configured at the time of the "make dist", which (1) may not be the
# configuration that the user wants, and (2) might cause link errors.
libbase_la_SOURCES = \
	Makefile.am \
	Makefile.in \
	bitvector.h \
	cvc4_assert.cpp \
	cvc4_assert.h \
	exception.cpp \
	exception.h \
	gmp_util.h \
	language.cpp \
	language.h \
	lemma_input_channel_forward.h \
	lemma_output_channel_forward.h \
	modal_exception.h \
	option_exception.h \
	output.cpp \
	output.h \
	printer_modes.cpp \
	printer_modes.h \
	quantifiers_modes.cpp \
	quantifiers_modes.h \
	simplification_mode.cpp \
	simplification_mode.h \
	theoryof_mode.cpp \
	theoryof_mode.h \
	ufss_mode.h



BUILT_SOURCES = \
	rational.h \
	integer.h \
	tls.h

if CVC4_CLN_IMP
libbase_la_SOURCES += \
	rational_cln_imp.cpp \
	integer_cln_imp.cpp
endif
if CVC4_GMP_IMP
libbase_la_SOURCES += \
	rational_gmp_imp.cpp \
	integer_gmp_imp.cpp
endif

EXTRA_DIST = \
	exception.i \
	rational_cln_imp.h \
	integer_cln_imp.h \
	integer_cln_imp.cpp \
	rational_cln_imp.cpp \
	rational_gmp_imp.h \
	integer_gmp_imp.h \
	integer_gmp_imp.cpp \
	rational_gmp_imp.cpp \
	rational.h.in \
	integer.h.in \
	integer.i \
	rational.i \
	tls.h.in \
	modal_exception.i \
	option_exception.i \
	language.i

DISTCLEANFILES = \
	integer.h.tmp \
	rational.h.tmp \
	integer.h \
	rational.h \
	tls.h.tmp \
	tls.h
