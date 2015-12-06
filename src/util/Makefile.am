AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libutil.la libstatistics.la

libstatistics_la_CPPFLAGS = $(CPPFLAGS) $(AM_CPPFLAGS) -D__BUILDING_STATISTICS_FOR_EXPORT


libutil_la_SOURCES = \
	backtrackable.h \
	Makefile.am \
	Makefile.in \
	debug.h \
	hash.h \
	bool.h \
	proof.h \
	result.h \
	result.cpp \
	configuration.h \
	configuration_private.h \
	configuration.cpp \
	ascription_type.h \
	array.h \
	datatype.h \
	datatype.cpp \
	tuple.h \
	record.h \
	record.cpp \
	divisible.h \
	divisible.cpp \
	maybe.h \
	matcher.h \
	sexpr.h \
	sexpr.cpp \
	statistics.h \
	statistics.cpp \
	statistics_registry.h \
	statistics_registry.cpp \
	dynamic_array.h \
	lemma_input_channel.h \
	lemma_output_channel.h \
	dense_map.h \
	channel.h \
	ntuple.h \
	subrange_bound.h \
	dump.h \
	dump.cpp \
	predicate.h \
	predicate.cpp \
	cardinality.h \
	cardinality.cpp \
	cache.h \
	utility.h \
	boolean_simplification.h \
	boolean_simplification.cpp \
	ite_removal.h \
	ite_removal.cpp \
	nary_builder.h \
	nary_builder.cpp \
	node_visitor.h \
	chain.h \
	index.h \
	uninterpreted_constant.h \
	uninterpreted_constant.cpp \
	abstract_value.h \
	abstract_value.cpp \
	array_store_all.h \
	array_store_all.cpp \
	emptyset.h \
	emptyset.cpp \
	model.h \
	model.cpp \
	sort_inference.h \
	sort_inference.cpp \
	regexp.h \
	regexp.cpp \
	bin_heap.h \
	didyoumean.h \
	didyoumean.cpp \
	unsat_core.h \
	unsat_core.cpp \
	floatingpoint.h \
	floatingpoint.cpp \
	resource_manager.h \
	resource_manager.cpp \
	unsafe_interrupt_exception.h

libstatistics_la_SOURCES = \
	statistics_registry.h \
	statistics_registry.cpp



EXTRA_DIST = \
	statistics.i \
	bool.i \
	sexpr.i \
	datatype.i \
	tuple.i \
	record.i \
	divisible.i \
	cardinality.i \
	result.i \
	configuration.i \
	subrange_bound.i \
	array.i \
	array_store_all.i \
	emptyset.i \
	ascription_type.i \
	hash.i \
	predicate.i \
	uninterpreted_constant.i \
	chain.i \
	regexp.i \
	resource_manager.i \
	unsafe_interrupt_exception.i \
	proof.i \
	unsat_core.i \
	floatingpoint.i
