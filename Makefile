HEADERS = graph.h c_program_timing.h sorting.h bitset.h vertex_ordering.h

all: russian_dolls colour_order

russian_dolls: russian_dolls.c graph.c c_program_timing.c vertex_ordering.c $(HEADERS)
	gcc -O3 -march=native -Wall -std=c11 -o russian_dolls \
		graph.c russian_dolls.c c_program_timing.c vertex_ordering.c

colour_order: colour_order.c graph.c c_program_timing.c vertex_ordering.c $(HEADERS)
	gcc -O3 -march=native -Wall -std=c11 -o colour_order \
		graph.c colour_order.c c_program_timing.c vertex_ordering.c

clean:
	rm colour_order
	rm russian_dolls
