CC      ?= cc
CFLAGS  ?= -O2 -Wall -Wextra
LDLIBS  ?= -lm

.PHONY: all test clean

all: test_zeros

test_zeros: test_zeros.c tw_add.c tw_add.h
	$(CC) $(CFLAGS) test_zeros.c tw_add.c $(LDLIBS) -o test_zeros

test: test_zeros
	./test_zeros

clean:
	rm -f test_zeros
