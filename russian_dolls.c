#define _GNU_SOURCE
#define _POSIX_SOURCE

#include "c_program_timing.h"
#include "graph.h"
#include "sorting.h"

#include <argp.h>
#include <limits.h>
#include <locale.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

const int num_permuted_graphs = 8;

typedef unsigned long long ULL;

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
    {"colouring-strategy", 'c', "STRATEGY", 0,
            "0=reverse, 1=forwards, 2=try lots of orders"},
    {"verbose-level", 'v', "LEVEL", 0,
            "Report progress up to level LEVEL of search tree"},
    {"vtx-ordering", 'o', "ORDER", 0,
            "Set vertex ordering heuristic (0=no sorting, 1=increasing deg, "
            "-1=decreasing deg, 2=increasing weight, -2=decreasing weight, "
            "3=increasing weighted degree, -3=decreasing weighted degree, "
            "4=increasing weighted degree plus weight, -4=decreasing weighted degree plus weight, "
            "9=increasing deg/wt, -9=decreasing deg/wt"},
    { 0 }
};

static struct {
    bool quiet;
    bool tavares_colour;
    int colouring_strategy;
    int verbose_level;
    int vtx_ordering;
    char *filename;
    int arg_num;
} arguments;

static error_t parse_opt (int key, char *arg, struct argp_state *state) {
    arguments.quiet = false;
    arguments.tavares_colour = false;
    arguments.verbose_level = 0;
    arguments.vtx_ordering = 0;
    arguments.filename = NULL;
    arguments.arg_num = 0;
    switch (key) {
        case 'q':
            arguments.quiet = true;
            break;
        case 't':
            arguments.tavares_colour = true;
            break;
        case 'c':
            arguments.colouring_strategy = atoi(arg);
            if (arguments.colouring_strategy<0 || arguments.colouring_strategy>2)
                fail("Invalid colouring strategy");
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
                                    Structs
*******************************************************************************/

struct VtxList {
    long total_wt;
    int size;
    int vv[MAX_N];
};

struct UnweightedVtxList {
    int size;
    int vv[MAX_N];
};

/*******************************************************************************
                                Bitset functions
*******************************************************************************/

static void set_bit(ULL bitset[WORDS_PER_BITSET], int bit) {
    bitset[bit/BITS_PER_WORD] |= (1ull << (bit%BITS_PER_WORD));
}

static void unset_bit(ULL bitset[WORDS_PER_BITSET], int bit) {
    bitset[bit/BITS_PER_WORD] &= ~(1ull << (bit%BITS_PER_WORD));
}

static int last_set_bit(ULL bitset[WORDS_PER_BITSET], int num_words) {
    for (int i=num_words-1; i>=0; i--) {
        if (bitset[i] != 0)
            return i*BITS_PER_WORD + (BITS_PER_WORD-1-__builtin_clzll(bitset[i]));
    }
    return -1;
}

static void reject_adjacent_vertices(ULL bitset[WORDS_PER_BITSET], ULL adj[WORDS_PER_BITSET],
        int num_words) {
    for (int i=0; i<num_words; i++) {
        bitset[i] &= ~adj[i];
    }
}

static void copy_bitset(ULL src[WORDS_PER_BITSET], ULL dest[WORDS_PER_BITSET],
        int num_words) {
    for (int i=0; i<num_words; i++)
        dest[i] = src[i];
}
/*******************************************************************************
                                Graph functions
*******************************************************************************/

void calculate_all_degrees(struct Graph *g) {
    for (int v=0; v<g->n; v++) {
        g->degree[v] = 0;
        for (int w=0; w<g->n; w++)
            g->degree[v] += g->adjmat[v][w];
    }
}

/*******************************************************************************
                                Other utilities
*******************************************************************************/

// Checks if a set of vertices induces a clique
bool check_clique(struct Graph* g, struct VtxList* clq) {
    long total_wt = 0;
    for (int i=0; i<clq->size; i++)
        total_wt += g->weight[clq->vv[i]];
    if (total_wt == clq->total_wt)
        return true;

    for (int i=0; i<clq->size-1; i++)
        for (int j=i+1; j<clq->size; j++)
            if (!g->adjmat[clq->vv[i]][clq->vv[j]])
                return false;
    return true;
}

/*******************************************************************************
                              Max clique functions
*******************************************************************************/

long weight[MAX_N]; 
long c[MAX_N]; 
bool adjacent[MAX_N][MAX_N];

struct PermutedGraph {
    int permutation[MAX_N];
    long wt[MAX_N];
    ULL bitadj[MAX_N][WORDS_PER_BITSET];
};

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

// Returns an upper bound on weight from the vertices in P
long tavares_colouring_bound(struct UnweightedVtxList *P, struct PermutedGraph *pg) {
    ULL to_colour[WORDS_PER_BITSET];
    ULL candidates[WORDS_PER_BITSET];

    int max_v = 0;
    for (int i=0; i<P->size; i++) {
        int v = pg->permutation[P->vv[i]];
//        int v = P->vv[i];
        if (v > max_v) max_v = v;
    }

    int numwords = max_v/BITS_PER_WORD+1;

    for (int i=0; i<numwords; i++)
        to_colour[i] = 0ull;

    for (int i=0; i<P->size; i++)
        set_bit(to_colour, pg->permutation[P->vv[i]]);
//        set_bit(to_colour, P->vv[i]);

    int v;
    long total_wt = 0;

    long residual_wt[MAX_N];
    for (int i=0; i<P->size; i++) {
        int v = pg->permutation[P->vv[i]];
        residual_wt[v] = pg->wt[v];
    }
//        residual_wt[P->vv[i]] = weight[P->vv[i]];


    while ((v=last_set_bit(to_colour, numwords))!=-1) {
        numwords = v/BITS_PER_WORD+1;
        copy_bitset(to_colour, candidates, numwords);
        long class_min_wt = residual_wt[v];
        unset_bit(to_colour, v);
        int col_class[MAX_N];
        int col_class_size = 1;
        col_class[0] = v;
        // The next line also removes v from the bitset
        reject_adjacent_vertices(candidates, pg->bitadj[v], numwords);
        while ((v=last_set_bit(candidates, v/BITS_PER_WORD+1))!=-1) {
            if (residual_wt[v] < class_min_wt) {
                class_min_wt = residual_wt[v];
            }
            unset_bit(to_colour, v);
            col_class[col_class_size++] = v;
            // The next line also removes v from the bitset
            reject_adjacent_vertices(candidates, pg->bitadj[v], v/BITS_PER_WORD+1);
        }
        for (int i=0; i<col_class_size; i++) {
            int w = col_class[i];
            residual_wt[w] -= class_min_wt;
            if (residual_wt[w] > 0) set_bit(to_colour, w);
        }
        total_wt += class_min_wt;
    }
    return total_wt;
}

// Returns an upper bound on weight from the vertices in P
long colouring_bound(struct UnweightedVtxList *P, struct PermutedGraph *pg) {
    ULL to_colour[WORDS_PER_BITSET];
    ULL candidates[WORDS_PER_BITSET];

    int max_v = 0;
    for (int i=0; i<P->size; i++) {
        int v = pg->permutation[P->vv[i]];
        if (v > max_v) max_v = v;
    }

    int numwords = max_v/BITS_PER_WORD+1;

    for (int i=0; i<numwords; i++)
        to_colour[i] = 0ull;

    for (int i=0; i<P->size; i++)
        set_bit(to_colour, pg->permutation[P->vv[i]]);

    int v;
    long total_wt = 0;

    while ((v=last_set_bit(to_colour, numwords))!=-1) {
        numwords = v/BITS_PER_WORD+1;
        copy_bitset(to_colour, candidates, numwords);
        long class_max_wt = pg->wt[v];
        total_wt += pg->wt[v];
        unset_bit(to_colour, v);
        // The next line also removes v from the bitset
        reject_adjacent_vertices(candidates, pg->bitadj[v], numwords);
        while ((v=last_set_bit(candidates, v/BITS_PER_WORD+1))!=-1) {
            if (pg->wt[v] > class_max_wt) {
                total_wt = total_wt - class_max_wt + pg->wt[v];
                class_max_wt = pg->wt[v];
            }
            unset_bit(to_colour, v);
            // The next line also removes v from the bitset
            reject_adjacent_vertices(candidates, pg->bitadj[v], v/BITS_PER_WORD+1);
        }
    }
    return total_wt;
}

void expand(struct VtxList *C, struct UnweightedVtxList *P,
        struct VtxList *incumbent, int level, struct PermutedGraph *permuted_graphs)
{
    stats.expand_calls += 1;
    if (P->size==0 && C->total_wt>incumbent->total_wt)
        *incumbent = *C;

    if (!arguments.tavares_colour || arguments.colouring_strategy != 2) {
        // Even if we're using a Tavares-style bound, try the simple colouring bound first;
        // (if we're not using colouring strategy 2)
        // it's faster, and if we're lucky it will prune
        for (int i=0; i < (arguments.colouring_strategy==2 ? num_permuted_graphs : 1); i++) {
            if (C->total_wt + colouring_bound(P, &permuted_graphs[i]) <= incumbent->total_wt) return;
        }
    }

    if (arguments.tavares_colour) {
        for (int i=0; i < (arguments.colouring_strategy==2 ? num_permuted_graphs : 1); i++) {
            long bound = C->total_wt + tavares_colouring_bound(P, &permuted_graphs[i]);
            if (bound <= incumbent->total_wt) return;
        }
    }

    struct UnweightedVtxList *new_P = &prealloc.P[level];

    for (int i=P->size-1; i>=0; i--) {
        int v = P->vv[i];
        if (C->total_wt + c[v] <= incumbent->total_wt) return;

        new_P->size = 0;
        for (int j=0; j<i; j++) {
            int w = P->vv[j];
            if (adjacent[v][w]) {
                new_P->vv[new_P->size++] = w;
            }
        }

        push_vtx(C, v);
        expand(C, new_P, incumbent, level+1, permuted_graphs);
        pop_vtx(C);
    }
}

double inc_deg_key(struct Graph *g, int v) { return g->degree[v]; }
double dec_deg_key(struct Graph *g, int v) { return -g->degree[v]; }
double inc_weighted_deg_key(struct Graph *g, int v) { return g->weighted_deg[v]; }
double dec_weighted_deg_key(struct Graph *g, int v) { return -g->weighted_deg[v]; }
double inc_weighted_deg_plus_wt_key(struct Graph *g, int v) { return g->weighted_deg[v] + g->weight[v]; }
double dec_weighted_deg_plus_wt_key(struct Graph *g, int v) { return -g->weighted_deg[v] - g->weight[v]; }
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

void carraghan_pardalos_order(int *vv, struct Graph *g, bool reverse) {
    int residual_weighted_deg[MAX_N];
    for (int i=0; i<g->n; i++)
        residual_weighted_deg[i] = g->weighted_deg[i];

    for (int i=0; i<g->n; i++) {
        // find vertex with lowest residual_weighted_deg
        int best_v = -1;
        long best_wt_deg = LONG_MAX;
        for (int j=i; j<g->n; j++) {
            int v = vv[j];
            if (residual_weighted_deg[v] < best_wt_deg) {
                best_wt_deg = residual_weighted_deg[v];
                best_v = v;
            }
        }
        int v = vv[best_v];
        vv[best_v] = vv[i];
        vv[i] = v;

        for (int j=i+1; j<g->n; j++) {
            int w = vv[j];
            if (g->adjmat[v][w])
                residual_weighted_deg[w] -= g->weight[v];
        }
    }

    if (reverse) {
        for (int i=0; i<g->n/2; i++) {
            int tmp = vv[i];
            vv[i] = vv[g->n - 1 - i];
            vv[g->n - 1 - i] = tmp;

        }
    }
}

void order_vertices(int *vv, struct Graph *g, int vtx_ordering) {
    for (int i=0; i<g->n; i++)
        vv[i] = i;

    switch(vtx_ordering) {
    case  0: break;  // no sorting
    case  1: INSERTION_SORT_VV(inc_deg_key) break;
    case -1: INSERTION_SORT_VV(dec_deg_key) break;
    case  2: INSERTION_SORT_VV(inc_wt_key) break;
    case -2: INSERTION_SORT_VV(dec_wt_key) break;
    case  3: calc_weighted_degs(g); INSERTION_SORT_VV(inc_weighted_deg_key) break;
    case -3: calc_weighted_degs(g); INSERTION_SORT_VV(dec_weighted_deg_key) break;
    case  4: calc_weighted_degs(g); INSERTION_SORT_VV(inc_weighted_deg_plus_wt_key) break;
    case -4: calc_weighted_degs(g); INSERTION_SORT_VV(dec_weighted_deg_plus_wt_key) break;
    case  5: calc_weighted_degs(g); carraghan_pardalos_order(vv, g, false); break;
    case -5: calc_weighted_degs(g); carraghan_pardalos_order(vv, g, true); break;
    case  9: INSERTION_SORT_VV(inc_wt_over_deg_key) break;
    case -9: INSERTION_SORT_VV(dec_wt_over_deg_key) break;
    case 10:
         // random permutation http://stackoverflow.com/a/15961211/3347737
         for (int i=g->n-1; i>0; i--) {
            int j = rand() % (i+1);
            int tmp = vv[i];
            vv[i] = vv[j];
            vv[j] = tmp;
         }
         break;
    default: fail("Unrecognised vertex order");
    }
}

void permute_graph(struct PermutedGraph *pg, int *vtx_order, struct Graph *g, int vtx_ordering) {
    int vv[MAX_N];
    order_vertices(vv, g, vtx_ordering);

    int vv_inv[MAX_N];
    for (int i=0; i<g->n; i++)
        vv_inv[vv[i]] = i;

    memset(pg, 0, sizeof(*pg));

    for (int i=0; i<g->n; i++) {
        int v = vtx_order[i];
        pg->permutation[i] = vv_inv[v];
        pg->wt[vv_inv[v]] = g->weight[v];
        for (int j=0; j<g->n; j++) {
            int w = vtx_order[j];
            bool is_adjacent = g->adjmat[v][w];
            if (i==j || is_adjacent)
                set_bit(pg->bitadj[vv_inv[v]], vv_inv[w]);
        }
    }
}
        

struct VtxList mc(struct Graph* g) {
    int vv[MAX_N];
    order_vertices(vv, g, arguments.vtx_ordering);

    for (int i=0; i<g->n; i++) {
        for (int j=0; j<g->n; j++) {
            adjacent[i][j] = g->adjmat[vv[i]][vv[j]];
        }
    }

    for (int i=0; i<g->n; i++)
        weight[i] = g->weight[vv[i]];

    struct PermutedGraph *permuted_graphs = malloc(num_permuted_graphs * sizeof(struct PermutedGraph));
    if (arguments.colouring_strategy == 0) {
        permute_graph(&permuted_graphs[0], vv, g, arguments.vtx_ordering);
    } else if (arguments.colouring_strategy == 1) {
        permute_graph(&permuted_graphs[0], vv, g, -arguments.vtx_ordering);
    } else {
        permute_graph(&permuted_graphs[0], vv, g, 1);
        permute_graph(&permuted_graphs[1], vv, g, -1);
        permute_graph(&permuted_graphs[2], vv, g, 2);
        permute_graph(&permuted_graphs[3], vv, g, -2);
        permute_graph(&permuted_graphs[4], vv, g, 3);
        permute_graph(&permuted_graphs[5], vv, g, -3);
        permute_graph(&permuted_graphs[6], vv, g, 9);
        permute_graph(&permuted_graphs[7], vv, g, -9);
        for (int i=8; i<num_permuted_graphs; i++)
            permute_graph(&permuted_graphs[i], vv, g, 10);
    }

    struct VtxList incumbent = {.size=0, .total_wt=0};

    for (int i=0; i<g->n; i++) {
        struct VtxList C = {.size=0, .total_wt=0};
        struct UnweightedVtxList P = {.size=0};
        push_vtx(&C, i);
        for (int j=0; j<i; j++)
            if (adjacent[i][j])
                P.vv[P.size++] = j;
        expand(&C, &P, &incumbent, 0, permuted_graphs);
        c[i] = incumbent.total_wt;
        if (!arguments.quiet)
            printf("c[%d]=%ld; Incumbent size: %d\n", i, c[i], incumbent.size);
    }

    // Use vertex indices from original graph
    for (int i=0; i<incumbent.size; i++)
        incumbent.vv[i] = vv[incumbent.vv[i]];

    free(permuted_graphs);

    return incumbent;
}

int main(int argc, char** argv) {
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
