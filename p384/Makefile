CFLAGS=-g -I/opt/local/include -O3 -fsanitize=address
CC=clang-mp-3.9
LDFLAGS=-lgmp -L/opt/local/lib -fsanitize=address
.PHONY: all
.PHONY: clean
all: p384_32_test p384_32_time p384_32_time_double p384_32_test_ecdsa p384_32_secgrind p384_64_test p384_64_time p384_64_time_double p384_64_test_ecdsa p384_64_secgrind
p384_32_test: p384_32_test.o p384_32.o
p384_32_time: p384_32_time.o p384_32.o
p384_32_time_double: p384_32_time_double.o p384_32.o
p384_32_test_ecdsa: p384_32_test_ecdsa.o p384_32.o
p384_32_secgrind: p384_32_secgrind.o p384_32.o
p384_64_test: p384_64_test.o p384_64.o
p384_64_time: p384_64_time.o p384_64.o
p384_64_time_double: p384_64_time_double.o p384_64.o
p384_64_test_ecdsa: p384_64_test_ecdsa.o p384_64.o
p384_64_secgrind: p384_64_secgrind.o p384_64.o
clean:
	rm -f *.o
	rm p384_32_test p384_32_time p384_32_time_double p384_32_test_ecdsa
