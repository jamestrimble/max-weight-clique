#define _GNU_SOURCE
#define _POSIX_SOURCE

#include "c_program_timing.h"
#include "graph.h"
#include "sorting.h"
#include "vertex_ordering.h"
#include "util.h"
#include "russian_dolls_solver.h"

#include <argp.h>
#include <limits.h>
#include <locale.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

/*******************************************************************************
                             Command-line arguments
*******************************************************************************/

static char doc[] = "Find a maximum clique in a graph in DIMACS format";
static char args_doc[] = "FILENAME";
static struct argp_option options[] = {
    {"quiet", 'q', 0, 0, "Quiet output"},
    {"colouring-type", 't', "TYPE", 0,
            "0=one vertex per colour, 1=one colour per vertex, 2=Tavares-style, 3=1 then 2"},
    {"colouring-order", 'k', "ORDER", 0, "0=reverse, 1=forwards"},
    {"vtx-ordering", 'o', "ORDER", 0, vertex_order_help},
    { 0 }
};

static struct {
    bool quiet;
    int colouring_type;
    int colouring_order;
    int vtx_ordering;
    char *filename;
    int arg_num;
} arguments;

void set_default_arguments() {
    arguments.quiet = false;
    arguments.colouring_type = 0;
    arguments.colouring_order = 0;
    arguments.vtx_ordering = 0;
    arguments.filename = NULL;
    arguments.arg_num = 0;
}

static error_t parse_opt (int key, char *arg, struct argp_state *state) {
    switch (key) {
        case 'q':
            arguments.quiet = true;
            break;
        case 't':
            arguments.colouring_type = atoi(arg);
            if (arguments.colouring_type<0 || arguments.colouring_type>3)
                fail("Invalid colouring type");
            break;
        case 'k':
            arguments.colouring_order = atoi(arg);
            if (arguments.colouring_order<0 || arguments.colouring_order>1)
                fail("Invalid colouring order");
            break;
        case 'o':
            arguments.vtx_ordering = atoi(arg);
            break;
        case ARGP_KEY_ARG:
            if (arguments.arg_num >= 1)
                argp_usage(state);
            arguments.filename = arg;
            arguments.arg_num++;
            break;
        case ARGP_KEY_END:
            if (arguments.arg_num == 0)
                argp_usage(state);
            break;
        default: return ARGP_ERR_UNKNOWN;
    }
    return 0;
}

static struct argp argp = { options, parse_opt, args_doc, doc };

/******************************************************************************/

int main(int argc, char** argv) {
    set_default_arguments();
    argp_parse(&argp, argc, argv, 0, 0, 0);

    struct Graph* g = calloc(1, sizeof(*g));
    readGraph(arguments.filename, g);

    long expand_call_count = 0;
    set_start_time();
    calculate_all_degrees(g);
    struct VtxList clq = mc(g, &expand_call_count, arguments.quiet,
            arguments.colouring_type, arguments.colouring_order, arguments.vtx_ordering);
    long elapsed_msec = get_elapsed_time_msec();

    // sort vertices in clique by index
    INSERTION_SORT(int, clq.vv, clq.size, clq.vv[j-1] > clq.vv[j])

    setlocale(LC_NUMERIC, "");
    printf("Weight of max clique: %ld\n", clq.total_wt);
    printf("Calls to expand():          %'15ld\n", expand_call_count);
    printf("Time:                       %15ld\n", elapsed_msec);

    for (int i=0; i<clq.size; i++)
        printf("%d ", clq.vv[i]+1);
    printf("\n");

    if (!check_clique(g, &clq))
        fail("*** Error: the set of vertices found do not induce a clique of the expected weight\n");

    free(g);
}
