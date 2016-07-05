CFLAGS=-g -O3 -m32
CC=clang-mp-3.9
LDFLAGS=-m32
.PHONY: all
all: p384_32_test p384_32_time p384_32_time_double
p384_32_test: p384_32_test.o p384_32.o
p384_32_time: p384_32_time.o p384_32.o
p384_32_time_double: p384_32_time_double.o p384_32.o
