CFLAGS=-Wall -O3

.PHONY: run
run: litmus
	while true; do ./$<; done

litmus: C-SB+o-mb-o+o-mb-o.litmus.c
	gcc $(CFLAGS) -S -o $@.s $< -pthread
	gcc $(CFLAGS) -o $@ $< -pthread
