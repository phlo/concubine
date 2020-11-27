CFLAGS=-Wall -O3

.PHONY: run
run: store-buffer.litmus
	while ./$<; do continue; done

store-buffer.litmus: store-buffer.litmus.c
	gcc $(CFLAGS) -S -o $@.s $< -pthread
	gcc $(CFLAGS) -o $@ $< -pthread
