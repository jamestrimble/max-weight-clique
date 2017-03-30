HEADERS = graph.h c_program_timing.h sorting.h bitset.h vertex_ordering.h util.h data.h
SHARED_C = graph.c c_program_timing.c vertex_ordering.c util.c bitset.c  data.c

all: russian_dolls colour_order

russian_dolls: russian_dolls.c russian_dolls_solver.c russian_dolls_solver.h $(SHARED_C) $(HEADERS)
	gcc -O3 -march=native -Wall -std=c11 -o russian_dolls russian_dolls.c russian_dolls_solver.c $(SHARED_C)

colour_order: colour_order.c colour_order_solver.c colour_order_solver.h $(SHARED_C) $(HEADERS)
	gcc -O3 -march=native -Wall -std=c11 -o colour_order colour_order.c colour_order_solver.c $(SHARED_C)

clean:
	rm colour_order
	rm russian_dolls
