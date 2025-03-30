CFLAGS=-nostdlib -nostdinc -fno-builtin -g3 -O0
CC=aarch64-linux-gnu-gcc

.PHONY: all clean

all: build/kernel.elf

build/kernel.elf: build/kernel_arm64.o build/head.o build/traps.o
	${CC} -T linker.lds -nostdlib -nostdinc -fno-builtin -g3 -O0 -static $^ -o $@

run: build/kernel.elf
	qemu-system-aarch64 -machine virt,virtualization=on,highmem=off,secure=off -cpu cortex-a53 -nographic  -m size=2G  -kernel $<

clean:
	rm -rf build/

build/head.o: head.S
	${CC} -c -march=armv8-a  $< -o $@

build/traps.o: traps.S
	${CC} ${CFLAGS} -c -march=armv8-a  $< -o $@

build/kernel_arm64.o: kernel_arm64.c
	mkdir -p build/
	${CC} ${CFLAGS} -c $< -o $@
