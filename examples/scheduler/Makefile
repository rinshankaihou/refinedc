all: fdsched

headers := $(wildcard include/*.h)

CPPFLAGS += -Iinclude/
vpath %.c src/

exceptions := -Wno-unused-parameter -Wno-gnu-designator -fdouble-square-bracket-attributes -Wno-unknown-attributes

CFLAGS += -std=gnu11 -Wall -Wextra -pedantic ${exceptions}

obj-fdsched = main.o fdsched.o io.o
fdsched: ${obj-fdsched}
	${CC} -o fdsched ${obj-fdsched}

run: fdsched
	./fdsched

clean:
	rm -f fdsched *.o
