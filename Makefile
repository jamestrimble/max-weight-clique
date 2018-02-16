HEADERS = graph.h c_program_timing.h sorting.h vertex_ordering.h util.h
SHARED_C = graph.c c_program_timing.c vertex_ordering.c util.c

all: colour_order colour_order_debug colour_order_very_verbose colour_order_print_bound_and_exit

colour_order: colour_order.c colour_order_solver.c colour_order_solver.h $(SHARED_C) $(HEADERS)
	gcc -O3 -march=native -Wall -std=c11 -o colour_order -DNDEBUG colour_order.c colour_order_solver.c $(SHARED_C)

colour_order_very_verbose: colour_order.c colour_order_solver.c colour_order_solver.h $(SHARED_C) $(HEADERS)
	gcc -O3 -march=native -Wall -std=c11 -o colour_order_very_verbose -DVERY_VERBOSE colour_order.c colour_order_solver.c $(SHARED_C)

colour_order_debug: colour_order.c colour_order_solver.c colour_order_solver.h $(SHARED_C) $(HEADERS)
	gcc -O0 -g -ggdb -march=native -Wall -std=c11 -o colour_order_debug colour_order.c colour_order_solver.c $(SHARED_C)

colour_order_print_bound_and_exit: colour_order.c colour_order_solver.c colour_order_solver.h $(SHARED_C) $(HEADERS)
	gcc -O3 -g -ggdb -march=native -Wall -std=c11 -o colour_order_print_bound_and_exit -DPRINT_BOUND_AND_EXIT colour_order.c colour_order_solver.c $(SHARED_C)

clean:
	rm colour_order colour_order_debug colour_order_very_verbose *.gcov *.gcda *.gcno
