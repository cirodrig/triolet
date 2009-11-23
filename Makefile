
include mk/flags.mk
include mk/programs.mk

# All targets in a normal build
BUILD_TARGETS= \
	src/compiler/ast/operators.$(SOEXT) \
	bin/pyon

###############################################################################
# Targets

.PHONY : all clean veryclean

all : $(BUILD_TARGETS)

clean :
	rm -f src/compiler/Python.hs	# autogenerated
	find src \( -name "*.o" \
		-o -name "*.hi" \
		-o -name "*.pyc" \
		-o -name "*.$(SOEXT)" \
		-o -name "*_stub.[ch]" \) -exec rm {} \;

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
# Program 'pyon'

PYON_C_SRCS=src/compiler/Main_c.c
PYON_C_GENERATED_SRCS=src/compiler/Parser/Driver_stub.c
PYON_HS_SRCS=src/compiler/Main.hs \
	src/compiler/Parser/Driver.hs \
	src/compiler/Parser/Parser.hs \
	src/compiler/Parser/Output.hs \
	src/compiler/Parser/ParserSyntax.hs
PYON_HS_GENERATED_SRCS=src/compiler/Python.hs

PYON_HS_OBJECTS=$(patsubst %.hs, %.o, $(PYON_HS_SRCS) $(PYON_HS_GENERATED_SRCS))
PYON_C_OBJECTS=$(patsubst %.c, %.o, $(PYON_C_SRCS) $(PYON_C_GENERATED_SRCS))
PYON_OBJECTS=$(PYON_HS_OBJECTS) $(PYON_C_OBJECTS)

bin/pyon : bin $(PYON_OBJECTS)
	$(HC) $(PYON_OBJECTS) -o $@ \
		$(HSCPY_X_OPTS) $(HSCPY_X_LIBDIRS) $(HSCPY_X_LIBS) \
		-package language-python-0.1.1 -package mtl

src/compiler/Main_c.o : src/compiler/Main_c.c
	$(CC) -c $< -o $@ $(HSCPY_C_OPTS) $(HSCPY_C_INCLUDEDIRS)

src/compiler/Parser/Driver_stub.o : src/compiler/Parser/Driver_stub.c
	$(CC) -c $< -o $@ $(CHS_C_OPTS) $(CHS_C_INCLUDEDIRS)

# Dependences
src/compiler/Main_c.o : src/compiler/Parser/Driver_stub.h
src/compiler/Main.o : src/compiler/Parser/Driver_stub.h
src/compiler/Main.o : src/compiler/Python.hi
src/compiler/Parser/Driver_stub.c \
 src/compiler/Parser/Driver_stub.h \
 src/compiler/Parser/Driver.o : src/compiler/Python.hi
src/compiler/Parser/Driver_stub.c \
 src/compiler/Parser/Driver_stub.h \
 src/compiler/Parser/Driver.o : src/compiler/Parser/Parser.hi
src/compiler/Parser/Driver_stub.c \
 src/compiler/Parser/Driver_stub.h \
 src/compiler/Parser/Driver.o : src/compiler/Parser/Output.hi
src/compiler/Parser/Output.o : src/compiler/Python.hi
src/compiler/Parser/Output.o : src/compiler/Parser/ParserSyntax.hi
src/compiler/Parser/Parser.o : src/compiler/Parser/ParserSyntax.hi

src/compiler/Main_c.o : src/compiler/Main_c.c
	$(CC) -c $< -o $@ $(HSCPY_C_OPTS) $(HSCPY_C_INCLUDEDIRS)

src/compiler/Parser/Driver_stub.o : src/compiler/Parser/Driver_stub.c
	$(CC) -c $< -o $@ $(CHS_C_OPTS) $(CHS_C_INCLUDEDIRS)

# After invoking the compiler,
# touch interface files to ensure that their timestamps are updated
define PYON_COMPILE_HS_SOURCE
$(patsubst %.hs, %.o, $(1)) : $(1)
	$(HC) -c $$< -o $$@ \
		$(HS_C_OPTS) $(HS_C_INCLUDEDIRS) \
		-isrc/compiler \
		-package language-python-0.1.1
	touch $(patsubst %.hs, %.hi, $(1))

endef

$(eval $(call PYON_COMPILE_HS_SOURCE, src/compiler/Main.hs))
$(eval $(call PYON_COMPILE_HS_SOURCE, src/compiler/Python.hs))
$(eval $(call PYON_COMPILE_HS_SOURCE, src/compiler/Parser/Parser.hs))
$(eval $(call PYON_COMPILE_HS_SOURCE, src/compiler/Parser/Output.hs))
$(eval $(call PYON_COMPILE_HS_SOURCE, src/compiler/Parser/ParserSyntax.hs))

# 'Driver.hs' has multiple targets, so it needs a distinct rule
src/compiler/Parser/Driver_stub.c \
 src/compiler/Parser/Driver_stub.h \
 src/compiler/Parser/Driver.o : src/compiler/Parser/Driver.hs
	$(HC) -c $< -o src/compiler/Parser/Driver.o \
		$(HS_C_OPTS) $(HS_C_INCLUDEDIRS) \
		-isrc/compiler
	touch src/compiler/Driver.hi

src/compiler/Python.hs : src/compiler/Python.hsc
	hsc2hs $< -o $@ $(HSCPY_C_INCLUDEDIRS)

###############################################################################
# Generic rules

%.hi : %.o ;
