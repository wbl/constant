CFLAGS = -g -I/opt/local/include -Wall -O3 -m32
LDFLAGS=-lgmp -L/opt/local/lib -m32
CC = gcc-mp-6
.PHONY: all
.PHONY: clean
all: p521_32_dh_test p521_32_dh_time p521_32_kat_test
p521_32_kat_test: p521_32.o p521_32_kat_test.o
p521_32_dh_test: p521_32.o p521_32_dh_test.o
p521_32_dh_time: p521_32.o p521_32_dh_time.o
p521_32_test_ecdsa: p521_32.o p521_32_test_ecdsa.o
clean:
	rm -f *.o
	rm -f p521_32_dh_test p521_32_dh_time p521_32_kat_test p521_32_test_ecdsa
