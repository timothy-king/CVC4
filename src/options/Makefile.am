# How options are built:
# Step 1: Copy the X_options source file into builddir as X_options.tmp.
#    X_options.tmp is a .PHONY rule to force this step to always be done.
# Step 2: Compare X_options.tmp to X_options.options.
#   If they are different, overwrite "X_options.options".
#   This is the file that we use to generate options from.
#   This is always up to dat with X_options. The change in name is just
#   to keep Makefile stage more explicit.
# Step 3: Generate X_options.sed from X_options.options using mkoptions.
# Step 4: Generate X_options.h from X_options.sed
# Step 5: Generate X_options.cpp from X_options.sed.
#   This stage also waits for X_options.h as otherwise it cannot compile.
# 

OPTIONS_SRC_FILES = \
	arith_options \
	arrays_options \
	base_options \
	booleans_options \
	builtin_options \
	bv_options \
	datatypes_options \
	decision_options \
	expr_options \
	fp_options \
	idl_options \
	main_options \
	parser_options \
	printer_options \
	proof_options \
	prop_options \
	quantifiers_options \
	sets_options \
	smt_options \
	strings_options \
	theory_options \
	uf_options

OPTIONS_TEMPS = \
	arith_options.tmp \
	arrays_options.tmp \
	base_options.tmp \
	booleans_options.tmp \
	builtin_options.tmp \
	bv_options.tmp \
	datatypes_options.tmp \
	decision_options.tmp \
	expr_options.tmp \
	fp_options.tmp \
	idl_options.tmp \
	main_options.tmp \
	parser_options.tmp \
	printer_options.tmp \
	proof_options.tmp \
	prop_options.tmp \
	quantifiers_options.tmp \
	sets_options.tmp \
	smt_options.tmp \
	strings_options.tmp \
	theory_options.tmp \
	uf_options.tmp

OPTIONS_OPTIONS_FILES = \
	arith_options.options \
	arrays_options.options \
	base_options.options \
	booleans_options.options \
	builtin_options.options \
	bv_options.options \
	datatypes_options.options \
	decision_options.options \
	expr_options.options \
	fp_options.options \
	idl_options.options \
	main_options.options \
	parser_options.options \
	printer_options.options \
	proof_options.options \
	prop_options.options \
	quantifiers_options.options \
	sets_options.options \
	smt_options.options \
	strings_options.options \
	theory_options.options \
	uf_options.options

OPTIONS_SEDS = \
	arith_options.sed \
	arrays_options.sed \
	base_options.sed \
	booleans_options.sed \
	builtin_options.sed \
	bv_options.sed \
	datatypes_options.sed \
	decision_options.sed \
	expr_options.sed \
	fp_options.sed \
	idl_options.sed \
	main_options.sed \
	parser_options.sed \
	printer_options.sed \
	proof_options.sed \
	prop_options.sed \
	quantifiers_options.sed \
	sets_options.sed \
	smt_options.sed \
	strings_options.sed \
	theory_options.sed \
	uf_options.sed

OPTIONS_HEADS = \
	arith_options.h \
	arrays_options.h \
	base_options.h \
	booleans_options.h \
	builtin_options.h \
	bv_options.h \
	datatypes_options.h \
	decision_options.h \
	expr_options.h \
	fp_options.h \
	idl_options.h \
	main_options.h \
	parser_options.h \
	printer_options.h \
	proof_options.h \
	prop_options.h \
	quantifiers_options.h \
	sets_options.h \
	smt_options.h \
	strings_options.h \
	theory_options.h \
	uf_options.h

OPTIONS_CPPS = \
	arith_options.cpp \
	arrays_options.cpp \
	base_options.cpp \
	booleans_options.cpp \
	builtin_options.cpp \
	bv_options.cpp \
	datatypes_options.cpp \
	decision_options.cpp \
	expr_options.cpp \
	fp_options.cpp \
	idl_options.cpp \
	main_options.cpp \
	parser_options.cpp \
	printer_options.cpp \
	proof_options.cpp \
	prop_options.cpp \
	quantifiers_options.cpp \
	sets_options.cpp \
	smt_options.cpp \
	strings_options.cpp \
	theory_options.cpp \
	uf_options.cpp


CPP_TEMPLATE_FILES = \
	base_options_template.h \
	base_options_template.cpp \
	options_holder_template.h \
	options_template.cpp \
	option_handler_get_option_template.cpp \
	option_handler_set_option_template.cpp

CPP_TEMPLATE_SEDS = \
	base_options_template.h.sed \
	base_options_template.cpp.sed \
	options_holder_template.h.sed \
	options_template.cpp.sed \
	option_handler_get_option_template.cpp.sed \
	option_handler_set_option_template.cpp.sed


DOCUMENTATION_FILES = \
	../../doc/cvc4.1 \
	../../doc/libcvc4.3 \
	../../doc/SmtEngine.3cvc \
	../../doc/options.3cvc

DOCUMENTATION_TEMPLATE_FILES = \
	../../doc/cvc4.1_template \
	../../doc/libcvc4.3_template \
	../../doc/SmtEngine.3cvc_template \
	../../doc/options.3cvc_template

DOCUMENTATION_TEMPLATE_SEDS = \
	../../doc/cvc4.1_template.sed \
	../../doc/libcvc4.3_template.sed \
	../../doc/SmtEngine.3cvc_template.sed \
	../../doc/options.3cvc_template.sed

AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/.. -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = liboptions.la

liboptions_la_SOURCES = \
	arith_heuristic_pivot_rule.cpp \
	arith_heuristic_pivot_rule.h \
	arith_propagation_mode.cpp \
	arith_propagation_mode.h \
	arith_unate_lemma_mode.cpp \
	arith_unate_lemma_mode.h \
	boolean_term_conversion_mode.cpp \
	boolean_term_conversion_mode.h \
	decision_mode.cpp \
	decision_mode.h \
	didyoumean.cpp \
	didyoumean.h \
	base_handlers.h \
	bv_bitblast_mode.cpp \
	bv_bitblast_mode.h \
	decision_weight.h \
	options.h \
	options_handler_interface.cpp \
	options_handler_interface.h

nodist_liboptions_la_SOURCES = \
	options.cpp \
	options_holder.h \
	$(OPTIONS_HEADS) \
	$(OPTIONS_CPPS) \
	option_handler_get_option.cpp \
	option_handler_set_option.cpp


BUILT_SOURCES = \
	exprs-builts \
	option_handler_get_option.cpp \
	option_handler_set_option.cpp \
	options.cpp \
	options_holder.h \
	$(OPTIONS_HEADS) \
	$(OPTIONS_CPPS) \
	$(OPTIONS_OPTIONS_FILES) \
	$(OPTIONS_SEDS) \
	$(CPP_TEMPLATE_SEDS) \
	$(DOCUMENTATION_TEMPLATE_SEDS) \
	$(DOCUMENTATION_FILES)

# listing {Debug,Trace}_tags too ensures that make doesn't auto-remove it
# after building (if it does, we don't get the "cached" effect with
# the .tmp files below, and we have to re-compile and re-link each
# time, even when there are no changes).
BUILT_SOURCES += \
	Debug_tags.h \
	Debug_tags \
	Trace_tags.h \
	Trace_tags

CLEANFILES = \
	$(OPTIONS_FILES_SRCS) \
	$(BUILT_SOURCES) \
	$(DOCUMENTATION_FILES)

EXTRA_DIST = \
	mkoptions \
	base_options_template.h \
	base_options_template.cpp \
	options_template.cpp \
	options_holder_template.h \
	options.i \
	options_handler_interface.i \
	option_handler_get_option_template.cpp \
	option_handler_set_option_template.cpp \
	$(OPTIONS_FILES_SRCS) \
	mktagheaders \
	mktags \
	$(DOCUMENTATION_FILES)


%_tags.h: %_tags mktagheaders
	$(AM_V_at)chmod +x @srcdir@/mktagheaders
	$(AM_V_GEN)( @srcdir@/mktagheaders "$<" "$<" ) >"$@"

# This .tmp business is to keep from having to re-compile options.cpp
# (and then re-link the libraries) if nothing has changed.
%_tags: %_tags.tmp
	$(AM_V_GEN)\
	diff -q "$^" "$@" &>/dev/null || mv "$^" "$@" || true
# .PHONY ensures the .tmp version is always rebuilt (to check for any changes)
.PHONY: Debug_tags.tmp Trace_tags.tmp
# The "sed" invocation below is particularly obnoxious, but it works around
# inconsistencies in REs on different platforms, using only a basic regular
# expression (no |, no \<, ...).
Debug_tags.tmp Trace_tags.tmp: mktags
	$(AM_V_at)chmod +x @srcdir@/mktags
	$(AM_V_GEN)(@srcdir@/mktags \
    '$(@:_tags.tmp=)' \
    "$$(find @srcdir@/../ -name '*.cpp' -o -name '*.h' -o -name '*.cc' -o -name '*.g')") >"$@"

MOSTLYCLEANFILES = \
	Debug_tags \
	Trace_tags \
	Debug_tags.tmp \
	Trace_tags.tmp \
	Debug_tags.h \
	Trace_tags.h

# Make sure the implicit rules never mistake a _template.cpp or _template.h file for source file.
options_holder_template.h options_template.cpp option_handler_get_option_template.cpp option_handler_set_option_template.cpp base_options_template.h base_options_template.cpp :;



# These are phony to force them to be made everytime.
.PHONY: arith_options.tmp arrays_options.tmp base_options.tmp booleans_options.tmp builtin_options.tmp bv_options.tmp datatypes_options.tmp decision_options.tmp expr_options.tmp fp_options.tmp idl_options.tmp main_options.tmp parser_options.tmp printer_options.tmp proof_options.tmp prop_options.tmp quantifiers_options.tmp sets_options.tmp smt_options.tmp strings_options.tmp theory_options.tmp uf_options.tmp

# Make is happier being listed explictly. Not sure why.
arith_options.tmp arrays_options.tmp base_options.tmp booleans_options.tmp builtin_options.tmp bv_options.tmp datatypes_options.tmp decision_options.tmp expr_options.tmp fp_options.tmp idl_options.tmp main_options.tmp parser_options.tmp printer_options.tmp proof_options.tmp prop_options.tmp quantifiers_options.tmp sets_options.tmp smt_options.tmp strings_options.tmp theory_options.tmp uf_options.tmp:
	echo "$@" "$(@:.tmp=)"
	$(AM_V_GEN)(cp "@srcdir@/$(@:.tmp=)" "$@")

%_options.options: %_options.tmp
	$(AM_V_GEN)\
	diff -q "$^" "$@" &>/dev/null || mv "$^" "$@" || true


# This bit is kinda tricky.
# We use the updating of %_options.options to signal that the options file updated.
# However, we use the original file in src to generate the file.
%_options.sed: %_options.options mkoptions
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions module-sed "@srcdir@/$(@:.sed=)" ) > "$@"


$(CPP_TEMPLATE_SEDS): %.sed : % mkoptions
#	echo "template seds"
#	echo "$@"
#	echo $(TEMPLATE_SEDS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions template-sed "$<" ) > "$@"

$(DOCUMENTATION_TEMPLATE_SEDS): %.sed : % mkoptions
#	echo "template seds"
#	echo "$@"
#	echo $(TEMPLATE_SEDS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions template-sed "$<" ) > "$@"

%_options.h : %_options.sed mkoptions base_options_template.h base_options_template.h.sed
#	echo heads
#	echo "$@"
#	echo $(OPTIONS_HEADS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/base_options_template.h \
		base_options_template.h.sed \
		"$<" \
	) > "$@"

summary.sed : mkoptions $(OPTIONS_OPTIONS_FILES)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions summary-sed \
		arith_options.options arrays_options.options base_options.options booleans_options.options builtin_options.options bv_options.options datatypes_options.options decision_options.options expr_options.options fp_options.options idl_options.options main_options.options parser_options.options printer_options.options proof_options.options prop_options.options quantifiers_options.options sets_options.options smt_options.options strings_options.options theory_options.options uf_options.options \
	) > summary.sed



#   mkoptions apply-sed-to-template sed-file template-file
options_holder.h : options_holder_template.h options_holder_template.h.sed summary.sed mkoptions $(OPTIONS_HEADS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/options_holder_template.h \
		@builddir@/options_holder_template.h.sed \
		summary.sed \
	) > "$@"

# Make sure not to match with "options.cpp" too.
%_options.cpp: %_options.sed %_options.h mkoptions options_holder.h base_options_template.cpp base_options_template.cpp.sed
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/base_options_template.cpp \
		base_options_template.cpp.sed \
		"$<" \
	) > "$@"


# # Bit of a hack here. The .h file needs to always be built before the .cpp file is compiled.
# $(OPTIONS_CPPS) : %.cpp : %.sed mkoptions base_options_template.cpp base_options_template.cpp.sed gen_heads_stamp
# #	echo "cpps"
# #	echo "$@"
# #	echo "$<"
# #	echo $(OPTIONS_CPPS)
# #	echo $(OPTIONS_FILES_SRCS)
# 	$(AM_V_at)chmod +x @srcdir@/mkoptions
# 	$(AM_V_at)mkdir -p `dirname "$@"`
# 	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
# 		@srcdir@/base_options_template.cpp \
# 		base_options_template.cpp.sed \
# 		"$<" \
# 	) > "$@"



#   mkoptions apply-sed-to-template sed-file template-file
options.cpp : options_template.cpp options_template.cpp.sed mkoptions summary.sed $(OPTIONS_HEADS) options_holder.h
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/options_template.cpp \
		@builddir@/options_template.cpp.sed \
		summary.sed \
	) > "$@"


#   mkoptions apply-sed-to-template sed-file template-file
option_handler_get_option.cpp : option_handler_get_option_template.cpp option_handler_get_option_template.cpp.sed mkoptions summary.sed $(OPTIONS_HEADS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/option_handler_get_option_template.cpp \
		@builddir@/option_handler_get_option_template.cpp.sed \
		summary.sed \
	) > "$@"

option_handler_set_option.cpp : option_handler_set_option_template.cpp option_handler_set_option_template.cpp.sed mkoptions summary.sed $(OPTIONS_HEADS)
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		@srcdir@/option_handler_set_option_template.cpp \
		@builddir@/option_handler_set_option_template.cpp.sed \
		summary.sed \
	) > "$@"



$(DOCUMENTATION_FILES) : % : %_template %_template.sed mkoptions summary.sed
#	echo "$<"
#	echo "$@"
	$(AM_V_at)chmod +x @srcdir@/mkoptions
	$(AM_V_GEN)(@srcdir@/mkoptions apply-sed-files-to-template \
		"$<" \
		"$<".sed \
		@builddir@/summary.sed \
	) > "$@"



#options-stamp: options_holder_template.h options_template.cpp smt_options_template.cpp base_options_template.h base_options_template.cpp mkoptions $(OPTIONS_FILE_SRCS)


# This rule is ugly.  It's needed to ensure that automake's dependence
# includes are available during distclean, even though they come from
# directories that are cleaned first.  Without this rule, "distclean"
# fails.
%.Plo:; $(MKDIR_P) "$(dir $@)" && : > "$@"

# Tim:
# This is insanely ugly and brittle!
# *Any* proposal to clean this up is welcomed!
# We are overloading automake's default distclean here. We have to overload
# distclean because otherwise it deletes the dependency directory
# "src/expr/.deps", then when running make distclean in src/expr it attempts to
# include .Plo files "defined in src/expr/.deps".
# An example from src/expr/Makefile.ina :
# @AMDEP_TRUE@@am__include@ @am__quote@./$(DEPDIR)/attribute.Plo@am__quote@
# The include must fail because this make file deleted that directory and
# distclean cannot proceed. So we override distclean to only remove
# "-rm -rf ./$(DEPDIR)". We then do manual massaging to finish up removing the
# extra files. To reproduce this, you can comment out the distclean below, run
# a distcheck and repeat this process.
# Why was this not a problem before? I do not know.
MANUAL_RM = \
	$(CLEANFILES) \
	../main/.dirstamp \
	../expr/.dirstamp \
	../options/options.lo \
	../options/base_options.lo \
	../options/.libs/options.o \
	../options/.libs/base_options.o \
	../options/.libs/liboptions.a \
	../options/Trace_tags.tmp \
	../options/Debug_tags.tmp \
	../options/liboptions.la \
	../parser/.dirstamp \
	../expr/.deps/options.Plo \
	../main/.deps/options.Plo \
	../parser/.deps/options.Plo \
	prop_options.lo \
	decision_options.lo \
	printer_options.lo \
	proof_options.lo \
	smt_options.lo \
	arith_options.lo \
	arrays_options.lo \
	booleans_options.lo \
	builtin_options.lo \
	bv_options.lo \
	datatypes_options.lo \
	fp_options.lo \
	idl_options.lo \
	quantifiers_options.lo \
	sets_options.lo \
	strings_options.lo \
	../theory/test_newalttheory/options.lo \
	../theory/test_newtheory/options.lo \
	uf_options.lo \
	theory_options.lo



distclean:
	-rm -rf ./$(DEPDIR)
	-rm -f Makefile
	-rm -f $(MANUAL_RM)

.PHONY: exprs-builts
exprs-builts:; $(AM_V_at)[ "$(FROM_EXPR)" != 1 ] && $(MAKE) -C ../expr builts || true

