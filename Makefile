
include mk/flags.mk
include mk/programs.mk

# All targets in a normal build
BUILD_TARGETS= \
	src/compiler/ast/operators.$(SOEXT)

###############################################################################
# Targets

.PHONY : all clean

all : $(BUILD_TARGETS)

clean :
	find src \( -name "*.o" -o -name "*.$(SOEXT)" \) -exec rm {} \;

###############################################################################
# Rules

src/compiler/ast/operators.o : src/compiler/ast/operators.h

src/compiler/ast/operators.o : src/compiler/ast/operators.c
	$(CC) -c $< -o $@ $(CPY_C_OPTS) $(CPY_C_INCLUDEDIRS)

src/compiler/ast/operators.$(SOEXT) : src/compiler/ast/operators.o
	$(LINKSHARED) $< -o $@ $(CPY_D_OPTS) $(CPY_D_LIBDIRS) $(CPY_D_LIBS)

