CC := gcc
CFLAGS := -O2 -Wall -g

.PHONY: default clean
default: galileo

galileo: galileo.o riscv-disas.o
	$(CC) galileo.o riscv-disas.o -lelf -o galileo

galileo.o: galileo.c riscv-disas.h
	$(CC) $(CFLAGS) -c galileo.c -o galileo.o

riscv-disas.o: riscv-disas.c riscv-disas.h
	$(CC) $(CFLAGS) -c riscv-disas.c -o riscv-disas.o

clean:
	-rm -f galileo.o riscv-disas.o galileo
