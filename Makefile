
include mk/flags.mk

# All targets in a normal build
BUILD_TARGETS= \
	src/compiler/ast/operators.so

###############################################################################
# Targets

.PHONY : all clean

all : $(BUILD_TARGETS)

clean :
	find src \( -name "*.o" -o -name "*.so" \) -exec rm {} \;

###############################################################################
# Rules

src/compiler/ast/operators.o : src/compiler/ast/operators.h

src/compiler/ast/operators.so : src/compiler/ast/operators.o
	$(CC) --shared $< -o $@

# Generic rules
include mk/rules.mk

