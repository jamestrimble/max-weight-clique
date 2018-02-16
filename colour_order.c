#define _GNU_SOURCE
#define _POSIX_SOURCE

#include "c_program_timing.h"
#include "graph.h"
#include "sorting.h"
#include "vertex_ordering.h"
#include "util.h"
#include "colour_order_solver.h"

#include <argp.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

static char doc[] = "Find a maximum clique in a graph in DIMACS format";
static char args_doc[] = "FILENAME";
static struct argp_option options[] = {
    {"quiet", 'q', 0, 0, "Quiet output"},
    {"colour-class-expansion", 'c', 0, 0, "Use colour class expansion"},
    {"vtx-ordering", 'o', "ORDER", 0, vertex_order_help},
    {"time-limit", 'l', "LIMIT", 0, "Time limit in seconds"},
    {"max-sat-level", 'm', "LEVEL", 0, "Level of MAXSAT reasoning (0, 1 or 2); default=2"},
    { 0 }
};

static struct {
    bool quiet;
    bool use_colour_class_expansion;
    int vtx_ordering;
    int time_limit;
    int max_sat_level;
    char *filename;
    int arg_num;
} arguments;

void set_default_arguments() {
    arguments.max_sat_level = 2;
}

static error_t parse_opt (int key, char *arg, struct argp_state *state) {
    switch (key) {
        case 'q':
            arguments.quiet = true;
            break;
        case 'c':
            arguments.use_colour_class_expansion = true;
            break;
        case 'o':
            arguments.vtx_ordering = atoi(arg);
            break;
        case 'l':
            arguments.time_limit = atoi(arg);
            break;
        case 'm':
            arguments.max_sat_level = atoi(arg);
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

    if (arguments.max_sat_level==0 && arguments.use_colour_class_expansion) {
        fail("The -m0 and -c flags cannot be used together.");
    }

    struct Graph* g = readGraph(arguments.filename);

    set_start_time();
    set_time_limit_sec(arguments.time_limit);
    long expand_call_count = 0;
    struct VtxList clq;
    init_VtxList(&clq, g->n);
    struct Params params = {
        .max_sat_level = arguments.max_sat_level,
        .vtx_ordering = arguments.vtx_ordering,
        .quiet = arguments.quiet,
        .use_colour_class_expansion = arguments.use_colour_class_expansion
    };
    mc(g, &expand_call_count, params, &clq);
    long elapsed_msec = get_elapsed_time_msec();
    if (is_timeout_flag_set()) {
        printf("TIMEOUT\n");
        elapsed_msec = arguments.time_limit * 1000;
    }

    // sort vertices in clique by index
    INSERTION_SORT(int, clq.vv, clq.size, clq.vv[j-1] > clq.vv[j])

    printf("Weight of max clique: %ld\n", clq.total_wt);
    printf("Calls to expand():          %ld\n", expand_call_count);
    printf("Time:                       %ld\n", elapsed_msec);

    for (int i=0; i<clq.size; i++)
        printf("%d ", clq.vv[i]+1);
    printf("\n");

    printf("Stats: size, weight of max weight clique, ms elapsed, node count\n");
    printf("%d %ld %ld %ld\n", clq.size, clq.total_wt, elapsed_msec, expand_call_count);

    if (!check_clique(g, &clq))
        fail("*** Error: the set of vertices found do not induce a clique of the expected weight\n");

    destroy_VtxList(&clq);
    free_graph(g);
}
