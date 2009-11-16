
include mk/flags.mk
include mk/programs.mk

PARSER_TARGET=bin/pyon_parser
PARSER_HS_SRCS=src/compiler/parser/Main.hs \
	src/compiler/parser/Parser.hs \
	src/compiler/parser/Python.hs \
	src/compiler/parser/PythonPrint.hs \
	src/compiler/parser/ParserSyntax.hs

PARSER_OBJECTS=$(patsubst %.hs, %.o, $(PARSER_HS_SRCS))

# All targets in a normal build
BUILD_TARGETS= \
	src/compiler/ast/operators.$(SOEXT) \
	$(PARSER_TARGET)

###############################################################################
# Targets

.PHONY : all clean veryclean

all : $(BUILD_TARGETS)

clean :
	find src \( -name "*.o" -o -name "*.hi" -o -name "*.pyc" -o -name "*.$(SOEXT)" \) -exec rm {} \;

veryclean : clean
	if [ -d bin ]; then rm -f bin/*; rmdir bin; fi

# Holds generated programs
bin :
	mkdir bin

###############################################################################
# Module 'operators'

src/compiler/ast/operators.$(SOEXT) : src/compiler/ast/operators.o
	$(LINKSHARED) $< -o $@ $(CPY_D_OPTS) $(CPY_D_LIBDIRS) $(CPY_D_LIBS)

src/compiler/ast/operators.o : src/compiler/ast/operators.h

src/compiler/ast/operators.o : src/compiler/ast/operators.c
	$(CC) -c $< -o $@ $(CPY_C_OPTS) $(CPY_C_INCLUDEDIRS)

###############################################################################
# Program 'pyon_parser'

bin/pyon_parser : bin $(PARSER_OBJECTS)
	$(HC) $(PARSER_OBJECTS) -o $@ \
		$(HSCPY_X_OPTS) $(HSCPY_X_LIBDIRS) $(HSCPY_X_LIBS) \
		-package language-python

src/compiler/parser/Python.hs : src/compiler/parser/Python.hsc
	hsc2hs $< -o $@ $(HSCPY_C_INCLUDEDIRS)

src/compiler/parser/Main.o : src/compiler/parser/Parser.hi
src/compiler/parser/Main.o : src/compiler/parser/Python.hi
src/compiler/parser/Main.o : src/compiler/parser/PythonPrint.hi
src/compiler/parser/PythonPrint.o : src/compiler/parser/Python.hi
src/compiler/parser/PythonPrint.o : src/compiler/parser/ParserSyntax.hi
src/compiler/parser/Parser.o : src/compiler/parser/ParserSyntax.hi
src/compiler/parser/Python.o : src/compiler/parser/ParserSyntax.hi

# After invoking the compiler,
# touch interface files to ensure that their timestamps are updated
define PARSER_COMPILE_HS_SOURCE
$(patsubst %.hs, %.o, $(1)) : $(1)
	$(HC) -c $$< -o $$@ \
		$(HS_C_OPTS) $(HS_C_INCLUDEDIRS) \
		-isrc/compiler/parser
	touch $$(patsubst %.o, %.hi, $$@)

endef

$(eval $(foreach src, $(PARSER_HS_SRCS), $(call PARSER_COMPILE_HS_SOURCE, $(src))))

###############################################################################
# Generic rules

%.hi : %.o ;
