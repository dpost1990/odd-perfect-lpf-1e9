# Build: needs GMP and primesieve (macOS: brew install gmp primesieve; Debian/Ubuntu: apt install libgmp-dev libprimesieve-dev)
CC      ?= cc
CFLAGS  ?= -O2 -march=native
PREFIX  ?= $(shell brew --prefix 2>/dev/null || echo /usr)
INC      = -I$(PREFIX)/include
LIB      = -L$(PREFIX)/lib

all: lpf review/lpf_exact review/rowverify review/mup_check review/rv_test review/xf_test

lpf: lpf.c
	$(CC) $(CFLAGS) $(INC) -o $@ $< $(LIB) -lgmp -lpthread -lm
review/lpf_exact: review/lpf_exact.c
	$(CC) $(CFLAGS) $(INC) -o $@ $< $(LIB) -lgmp -lpthread -lm
review/rowverify: review/rowverify.c review/rv_funcs.inc
	$(CC) $(CFLAGS) $(INC) -o $@ $< $(LIB) -lgmp -lprimesieve -lpthread -lm
review/mup_check: review/mup_check.c
	$(CC) $(CFLAGS) $(INC) -o $@ $< $(LIB) -lprimesieve -lm
review/rv_test: review/rv_test.c review/rv_funcs.inc
	$(CC) $(CFLAGS) $(INC) -o $@ $< $(LIB) -lgmp -lm
review/xf_test: review/xf_test.c
	$(CC) $(CFLAGS) $(INC) -o $@ $< $(LIB) -lgmp -lm

# quick end-to-end check at B = 10^6 (seconds): search, replay, tree check
check-small: all
	mkdir -p check-out
	./lpf 1000000 2 odd 2 check-out/lpf_rows_1e6.txt check-out/lpf_1e6.log
	python3 replay.py 1000000 check-out/lpf_rows_1e6.txt check-out/lpf_1e6.log
	review/mup_check 1000000 > check-out/lpf_mup_1e6.txt
	python3 review/tree_check.py 1000000 check-out/lpf_rows_1e6.txt check-out/lpf_1e6.log check-out/lpf_mup_1e6.txt

# re-check the published B = 10^9 certificate without re-running the search
check-1e9-replay:
	shasum -a 256 -c SHA256SUMS
	python3 replay.py 1000000000 runs/rows_1000000000.txt runs/c_1000000000.log
	python3 review/tree_check.py 1000000000 runs/rows_1000000000.txt runs/c_1000000000.log review/runs/mup_1000000000.txt

clean:
	rm -f lpf review/lpf_exact review/rowverify review/mup_check review/rv_test review/xf_test
.PHONY: all check-small check-1e9-replay clean
