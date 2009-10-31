
include mk/flags.mk
include mk/programs.mk

PARSER_TARGET=bin/pyon_parser
PARSER_OBJECTS=src/compiler/parser/Main.o \
	src/compiler/parser/Parser.o\
	src/compiler/parser/PythonPrint.o \
	src/compiler/parser/ParserSyntax.o

# All targets in a normal build
BUILD_TARGETS= \
	src/compiler/ast/operators.$(SOEXT) \
	$(PARSER_TARGET)

###############################################################################
# Targets

.PHONY : all clean

all : $(BUILD_TARGETS)

clean :
	if [ -d bin ]; then rm -f bin/*; rmdir bin; fi
	find src \( -name "*.o" -o -name "*.hi" -o -name "*.pyc" -o -name "*.$(SOEXT)" \) -exec rm {} \;

###############################################################################
# Rules

src/compiler/ast/operators.o : src/compiler/ast/operators.h

src/compiler/ast/operators.o : src/compiler/ast/operators.c
	$(CC) -c $< -o $@ $(CPY_C_OPTS) $(CPY_C_INCLUDEDIRS)

src/compiler/ast/operators.$(SOEXT) : src/compiler/ast/operators.o
	$(LINKSHARED) $< -o $@ $(CPY_D_OPTS) $(CPY_D_LIBDIRS) $(CPY_D_LIBS)

bin :
	mkdir bin

bin/pyon_parser : bin $(PARSER_OBJECTS)
	$(HC) $(PARSER_OBJECTS) -o $@ $(HSCPY_X_OPTS) $(HSCPY_X_LIBDIRS) $(HSCPY_X_LIBS) \
		-package language-python

src/compiler/parser/Main.o : src/compiler/parser/Parser.hi
src/compiler/parser/Main.o : src/compiler/parser/PythonPrint.hi
src/compiler/parser/Main.o : src/compiler/parser/Main.hs
	$(RM) -f $@
	$(HC) -c $< -o $@ $(HS_C_OPTS) $(HS_C_INCLUDEDIRS) -isrc/compiler/parser

src/compiler/parser/Parser.o : src/compiler/parser/ParserSyntax.hi
src/compiler/parser/Parser.o : src/compiler/parser/Parser.hs
	$(RM) -f $@
	$(HC) -c $< -o $@ $(HS_C_OPTS) $(HS_C_INCLUDEDIRS) -isrc/compiler/parser

src/compiler/parser/PythonPrint.o : src/compiler/parser/ParserSyntax.hi
src/compiler/parser/PythonPrint.o : src/compiler/parser/PythonPrint.hs
	$(RM) -f $@
	$(HC) -c $< -o $@ $(HS_C_OPTS) $(HS_C_INCLUDEDIRS) -isrc/compiler/parser

src/compiler/parser/ParserSyntax.o : src/compiler/parser/ParserSyntax.hs
	$(RM) -f $@
	$(HC) -c $< -o $@ $(HS_C_OPTS) $(HS_C_INCLUDEDIRS) -isrc/compiler/parser

%.hi : %.o ;
