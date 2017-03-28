#define _GNU_SOURCE
#define _POSIX_SOURCE

#include "c_program_timing.h"
#include "graph.h"
#include "sorting.h"
#include "bitset.h"

#include <argp.h>
#include <limits.h>
#include <locale.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


#define MIN(X, Y) (((X) < (Y)) ? (X) : (Y))

static void fail(char* msg) {
    printf("%s\n", msg);
    exit(1);
}

/*******************************************************************************
                             Command-line arguments
*******************************************************************************/

static char doc[] = "Find a maximum clique in a graph in DIMACS format";
static char args_doc[] = "FILENAME";
static struct argp_option options[] = {
    {"quiet", 'q', 0, 0,
            "Quiet output"},
    {"tavares-colour", 't', 0, 0,
            "Tavares-style colouring"},
    {"verbose-level", 'v', "LEVEL", 0,
            "Report progress up to level LEVEL of search tree"},
    {"vtx-ordering", 'o', "ORDER", 0,
            "Set vertex ordering heuristic (0=no sorting, 1=increasing deg, "
            "-1=decreasing deg, 2=increasing weight, -2=decreasing weight, "
            "9=increasing deg/wt, -9=decreasing deg/wt"},
    { 0 }
};

static struct {
    bool quiet;
    bool tavares_colour;
    int verbose_level;
    int vtx_ordering;
    char *filename;
    int arg_num;
} arguments;

void set_default_arguments() {
    arguments.quiet = false;
    arguments.tavares_colour = false;
    arguments.verbose_level = 0;
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
            arguments.tavares_colour = true;
            break;
        case 'v':
            arguments.verbose_level = atoi(arg);
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

/*******************************************************************************
                                     Stats
*******************************************************************************/

static struct {
    long expand_calls;
} stats;

void initialise_stats() {
    stats.expand_calls = 0;
}

/*******************************************************************************
                              Max clique functions
*******************************************************************************/

long weight[MAX_N]; 
bool adjacent[MAX_N][MAX_N];
unsigned long long bitadj[MAX_N][WORDS_PER_BITSET];

void push_vtx(struct VtxList *L, int v) {
    L->vv[L->size++] = v;
    L->total_wt += weight[v];
}

void pop_vtx(struct VtxList *L) {
    L->size--;
    L->total_wt -= weight[L->vv[L->size]];
}

struct {
    struct UnweightedVtxList P[MAX_N];
} prealloc;

void tavares_colouring_bound(struct UnweightedVtxList *P, long *cumulative_wt_bound) {
    unsigned long long to_colour[WORDS_PER_BITSET];
    unsigned long long candidates[WORDS_PER_BITSET];

    int max_v = 0;
    for (int i=0; i<P->size; i++)
        if (P->vv[i] > max_v)
            max_v = P->vv[i];

    int numwords = max_v/BITS_PER_WORD+1;

    for (int i=0; i<numwords; i++)
        to_colour[i] = 0ull;

    for (int i=0; i<P->size; i++)
        set_bit(to_colour, P->vv[i]);

    long residual_wt[MAX_N];
    for (int i=0; i<P->size; i++)
        residual_wt[P->vv[i]] = weight[P->vv[i]];

    int v;

    long bound = 0;

    P->size = 0;

    while ((v=last_set_bit(to_colour, numwords))!=-1) {
        numwords = v/BITS_PER_WORD+1;
        copy_bitset(to_colour, candidates, numwords);
        long class_min_wt = residual_wt[v];
        unset_bit(to_colour, v);
        int col_class[MAX_N];
        int col_class_size = 1;
        col_class[0] = v;
        // The next line also removes v from the bitset
        reject_adjacent_vertices(candidates, bitadj[v], numwords);
        while ((v=last_set_bit(candidates, v/BITS_PER_WORD+1))!=-1) {
            if (residual_wt[v] < class_min_wt)
                class_min_wt = residual_wt[v];
            unset_bit(to_colour, v);
            col_class[col_class_size++] = v;
            // The next line also removes v from the bitset
            reject_adjacent_vertices(candidates, bitadj[v], v/BITS_PER_WORD+1);
        }
        bound += class_min_wt;
        for (int i=0; i<col_class_size; i++) {
            int w = col_class[i];
            residual_wt[w] -= class_min_wt;
            if (residual_wt[w] > 0) {
                set_bit(to_colour, w);
            } else {
                cumulative_wt_bound[P->size] = bound;
                P->vv[P->size++] = w;
            }
        }
    }
}

struct ColourClass {
    int start;
    int size;
    long max_wt;
};

#define NUM_COLOUR_CLASS_LISTS 10

void sorted_colouring_bound(struct UnweightedVtxList *P, long *cumulative_wt_bound) {
    unsigned long long to_colour[WORDS_PER_BITSET];
    unsigned long long candidates[WORDS_PER_BITSET];
    int colour_class_buf[MAX_N];   // Lists of vertices in colour classes will be stored here
    int colour_class_buf_len = 0;
    struct ColourClass colour_classes[NUM_COLOUR_CLASS_LISTS][MAX_N];
    int colour_classes_len[NUM_COLOUR_CLASS_LISTS];

    for (int i=1; i<NUM_COLOUR_CLASS_LISTS; i++)
        colour_classes_len[i] = 0;

    int max_v = 0;
    for (int i=0; i<P->size; i++)
        if (P->vv[i] > max_v)
            max_v = P->vv[i];

    int numwords = max_v/BITS_PER_WORD+1;

    for (int i=0; i<numwords; i++)
        to_colour[i] = 0ull;

//    printf("*%d* ", P->size);
    for (int i=0; i<P->size; i++)
        set_bit(to_colour, P->vv[i]);

    int v;

    while ((v=last_set_bit(to_colour, numwords))!=-1) {
        int class_start = colour_class_buf_len;
        numwords = v/BITS_PER_WORD+1;
        copy_bitset(to_colour, candidates, numwords);
        long class_max_wt = weight[v];
        unset_bit(to_colour, v);
        colour_class_buf[colour_class_buf_len++] = v;
        // The next line also removes v from the bitset
        reject_adjacent_vertices(candidates, bitadj[v], numwords);
        while ((v=last_set_bit(candidates, v/BITS_PER_WORD+1))!=-1) {
            if (weight[v] > class_max_wt)
                class_max_wt = weight[v];
            unset_bit(to_colour, v);
            colour_class_buf[colour_class_buf_len++] = v;
            // The next line also removes v from the bitset
            reject_adjacent_vertices(candidates, bitadj[v], v/BITS_PER_WORD+1);
        }
        int class_sz = colour_class_buf_len - class_start;
        int list_idx = class_sz<NUM_COLOUR_CLASS_LISTS ? class_sz : NUM_COLOUR_CLASS_LISTS-1;
        colour_classes[list_idx][colour_classes_len[list_idx]++] = (struct ColourClass) {
                .start=class_start,
                .size=class_sz,
                .max_wt=class_max_wt};
    }

    P->size = 0;
    long bound = 0;
    for (int k=NUM_COLOUR_CLASS_LISTS-1; k>=1; k--) {
        for (int i=0; i<colour_classes_len[k]; i++) {
            struct ColourClass *cc = &colour_classes[k][i];
            bound += cc->max_wt;
            for (int j=0; j<cc->size; j++) {
                cumulative_wt_bound[P->size] = bound;
                P->vv[P->size++] = colour_class_buf[cc->start+j];
            }
        }
    }
}

void colouring_bound(struct UnweightedVtxList *P, long *cumulative_wt_bound) {
    unsigned long long to_colour[WORDS_PER_BITSET];
    unsigned long long candidates[WORDS_PER_BITSET];

    int max_v = 0;
    for (int i=0; i<P->size; i++)
        if (P->vv[i] > max_v)
            max_v = P->vv[i];

    int numwords = max_v/BITS_PER_WORD+1;

    for (int i=0; i<numwords; i++)
        to_colour[i] = 0ull;

//    printf("*%d* ", P->size);
    for (int i=0; i<P->size; i++)
        set_bit(to_colour, P->vv[i]);

    int v;

    P->size = 0;

    int j = 0;

    long bound = 0;

    while ((v=last_set_bit(to_colour, numwords))!=-1) {
        numwords = v/BITS_PER_WORD+1;
        copy_bitset(to_colour, candidates, numwords);
        long class_max_wt = weight[v];
        unset_bit(to_colour, v);
        P->vv[P->size++] = v;
        // The next line also removes v from the bitset
        reject_adjacent_vertices(candidates, bitadj[v], numwords);
        while ((v=last_set_bit(candidates, v/BITS_PER_WORD+1))!=-1) {
            if (weight[v] > class_max_wt)
                class_max_wt = weight[v];
            unset_bit(to_colour, v);
            P->vv[P->size++] = v;
            // The next line also removes v from the bitset
            reject_adjacent_vertices(candidates, bitadj[v], v/BITS_PER_WORD+1);
        }
        bound += class_max_wt;
        for (int k=j; k<P->size; k++)
            cumulative_wt_bound[k] = bound;
        j = P->size;
    }
}

void expand(struct VtxList *C, struct UnweightedVtxList *P, struct VtxList *incumbent, int level)
{
    stats.expand_calls += 1;
    if (P->size==0 && C->total_wt>incumbent->total_wt) {
        *incumbent = *C;
        printf("New incumbent of weight %ld\n", incumbent->total_wt);
    }

    long cumulative_wt_bound[MAX_N];

    if (arguments.tavares_colour)
        tavares_colouring_bound(P, cumulative_wt_bound);
    else
        colouring_bound(P, cumulative_wt_bound);

    struct UnweightedVtxList *new_P = &prealloc.P[level];

    for (int i=P->size-1; i>=0 && C->total_wt+cumulative_wt_bound[i]>incumbent->total_wt; i--) {
        int v = P->vv[i];

        new_P->size = 0;
        for (int j=0; j<i; j++) {
            int w = P->vv[j];
            if (adjacent[v][w]) {
                new_P->vv[new_P->size++] = w;
            }
        }

        push_vtx(C, v);
        expand(C, new_P, incumbent, level+1);
        pop_vtx(C);
    }
}

double inc_deg_key(struct Graph *g, int v) { return g->degree[v]; }
double dec_deg_key(struct Graph *g, int v) { return -g->degree[v]; }
double inc_weighted_deg_key(struct Graph *g, int v) { return g->weighted_deg[v]; }
double dec_weighted_deg_key(struct Graph *g, int v) { return -g->weighted_deg[v]; }
double inc_wt_key(struct Graph *g, int v) { return g->weight[v]; }
double dec_wt_key(struct Graph *g, int v) { return -g->weight[v]; }

double inc_wt_over_deg_key(struct Graph *g, int v) {
    return (double)g->weight[v] / g->degree[v];
}
double dec_wt_over_deg_key(struct Graph *g, int v) {
    return -(double)g->weight[v] / g->degree[v];
}

void calc_weighted_degs(struct Graph *g) {
    for (int i=0; i<g->n; i++) {
        g->weighted_deg[i] = 0;
        for (int j=0; j<g->n; j++) {
            if (g->adjmat[i][j]) {
                g->weighted_deg[i] += g->weight[j];
            }
        }
    }
}

struct VtxList mc(struct Graph* g) {
    int vv[MAX_N];
    for (int i=0; i<g->n; i++)
        vv[i] = i;

    switch(arguments.vtx_ordering) {
    case  0: break;  // no sorting
    case  1: INSERTION_SORT_VV(inc_deg_key) break;
    case -1: INSERTION_SORT_VV(dec_deg_key) break;
    case  2: INSERTION_SORT_VV(inc_wt_key) break;
    case -2: INSERTION_SORT_VV(dec_wt_key) break;
    case  3: calc_weighted_degs(g); INSERTION_SORT_VV(inc_weighted_deg_key) break;
    case -3: calc_weighted_degs(g); INSERTION_SORT_VV(dec_weighted_deg_key) break;
    case  9: INSERTION_SORT_VV(inc_wt_over_deg_key) break;
    case -9: INSERTION_SORT_VV(dec_wt_over_deg_key) break;
    default: fail("Unrecognised vertex order");
    }

    memset(bitadj, 0, sizeof(bitadj));
    for (int i=0; i<g->n; i++) {
        for (int j=0; j<g->n; j++) {
            adjacent[i][j] = g->adjmat[vv[i]][vv[j]];
            if (i==j || adjacent[i][j])
                set_bit(bitadj[i], j);
        }
    }

    for (int i=0; i<g->n; i++)
        weight[i] = g->weight[vv[i]];

    struct VtxList incumbent = {.size=0, .total_wt=0};

    struct UnweightedVtxList P = {.size=0};
    for (int v=0; v<g->n; v++) P.vv[P.size++] = v;
    struct VtxList C = {.size=0, .total_wt=0};
    expand(&C, &P, &incumbent, 0);

    // Use vertex indices from original graph
    for (int i=0; i<incumbent.size; i++)
        incumbent.vv[i] = vv[incumbent.vv[i]];

    return incumbent;
}

int main(int argc, char** argv) {
    set_default_arguments();
    argp_parse(&argp, argc, argv, 0, 0, 0);

    initialise_stats();

    struct Graph* g = calloc(1, sizeof(*g));
    readGraph(arguments.filename, g);

    set_start_time();
    calculate_all_degrees(g);
    struct VtxList clq = mc(g);
    long elapsed_msec = get_elapsed_time_msec();

    // sort vertices in clique by index
    INSERTION_SORT(int, clq.vv, clq.size, clq.vv[j-1] > clq.vv[j])

    setlocale(LC_NUMERIC, "");
    printf("Weight of max clique: %ld\n", clq.total_wt);
    printf("Calls to expand():          %'15ld\n", stats.expand_calls);
    printf("Time:                       %15ld\n", elapsed_msec);

    for (int i=0; i<clq.size; i++)
        printf("%d ", clq.vv[i]+1);
    printf("\n");

    if (!check_clique(g, &clq))
        fail("*** Error: the set of vertices found do not induce a clique of the expected weight\n");

    free(g);
}
