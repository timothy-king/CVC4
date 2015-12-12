AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libutil.la libstatistics.la

libstatistics_la_CPPFLAGS = $(CPPFLAGS) $(AM_CPPFLAGS) -D__BUILDING_STATISTICS_FOR_EXPORT


# Do not list built sources (like integer.h, rational.h) here!
# Rather, list them under BUILT_SOURCES, and their .in versions under
# EXTRA_DIST.  Otherwise, they're packaged up in the tarball, which is
# no good---they belong in the configured builds/ directory.  If they
# end up in the source directory, they build the cvc4 that was
# configured at the time of the "make dist", which (1) may not be the
# configuration that the user wants, and (2) might cause link errors.
libutil_la_SOURCES = \
	Makefile.am \
	Makefile.in \
	abstract_value.cpp \
	abstract_value.h \
	bin_heap.h \
	bitvector.h \
	bool.h \
	cache.h \
	cardinality.cpp \
	cardinality.h \
	channel.h \
	configuration.cpp \
	configuration.h \
	configuration_private.h \
	debug.h \
	dense_map.h \
	divisible.cpp \
	divisible.h \
	dump.cpp \
	dump.h \
	dynamic_array.h \
	emptyset.cpp \
	emptyset.h \
	floatingpoint.cpp \
	floatingpoint.h \
	gmp_util.h \
	hash.h \
	index.h \
	lemma_input_channel.h \
	lemma_output_channel.h \
	matcher.h \
	maybe.h \
	model.cpp \
	model.h \
	nary_builder.cpp \
	nary_builder.h \
	node_visitor.h \
	ntuple.h \
	predicate.cpp \
	predicate.h \
	proof.h \
	record.cpp \
	record.h \
	regexp.cpp \
	regexp.h \
	resource_manager.cpp \
	resource_manager.h \
	result.cpp \
	result.h \
	sort_inference.cpp \
	sort_inference.h \
	smt2_quote_string.cpp \
	smt2_quote_string.h \
	statistics.cpp \
	statistics.h \
	statistics_registry.cpp \
	statistics_registry.h \
	subrange_bound.h \
	tuple.h \
	uninterpreted_constant.cpp \
	uninterpreted_constant.h \
	unsafe_interrupt_exception.h \
	unsat_core.cpp \
	unsat_core.h \
	utility.h

libstatistics_la_SOURCES = \
	statistics_registry.h \
	statistics_registry.cpp

BUILT_SOURCES = \
	rational.h \
	integer.h

if CVC4_CLN_IMP
libutil_la_SOURCES += \
	rational_cln_imp.cpp \
	integer_cln_imp.cpp
endif
if CVC4_GMP_IMP
libutil_la_SOURCES += \
	rational_gmp_imp.cpp \
	integer_gmp_imp.cpp
endif


EXTRA_DIST = \
	bitvector.i \
	bool.i \
	cardinality.i \
	configuration.i \
	divisible.i \
	emptyset.i \
	floatingpoint.i \
	hash.i \
	integer.h.in \
	integer.i \
	integer_cln_imp.cpp \
	integer_cln_imp.h \
	integer_gmp_imp.cpp \
	integer_gmp_imp.h \
	predicate.i \
	proof.i \
	rational.h.in \
	rational.i \
	rational_cln_imp.cpp \
	rational_cln_imp.h \
	rational_gmp_imp.cpp \
	rational_gmp_imp.h \
	record.i \
	regexp.i \
	resource_manager.i \
	result.i \
	statistics.i \
	subrange_bound.i \
	tuple.i \
	uninterpreted_constant.i \
	unsafe_interrupt_exception.i \
	unsat_core.i


DISTCLEANFILES = \
	integer.h.tmp \
	rational.h.tmp \
	integer.h \
	rational.h
