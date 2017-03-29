#define _GNU_SOURCE
#define _POSIX_SOURCE

#include "c_program_timing.h"
#include "graph.h"
#include "sorting.h"
#include "bitset.h"
#include "vertex_ordering.h"
#include "util.h"
#include "russian_dolls_solver.h"

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void push_vtx(struct Graph *g, struct VtxList *L, int v) {
    L->vv[L->size++] = v;
    L->total_wt += g->weight[v];
}

void pop_vtx(struct Graph *g, struct VtxList *L) {
    L->size--;
    L->total_wt -= g->weight[L->vv[L->size]];
}

struct {
    struct UnweightedVtxList P[MAX_N];
} prealloc;

// Returns an upper bound on weight from the vertices in P
long colouring_bound(struct Graph *g, struct UnweightedVtxList *P, bool tavares_style,
        int (*next_vtx_fun)(unsigned long long *, int))
{
    unsigned long long to_colour[WORDS_PER_BITSET];
    unsigned long long candidates[WORDS_PER_BITSET];

    if (P->size==0) return 0;

    int max_v = P->vv[P->size-1];
    int numwords = max_v/BITS_PER_WORD+1;

    for (int i=0; i<numwords; i++)
        to_colour[i] = 0ull;

    for (int i=0; i<P->size; i++)
        set_bit(to_colour, P->vv[i]);

    int v;
    long total_wt = 0;

    if (tavares_style) {
        long residual_wt[MAX_N];
        for (int i=0; i<P->size; i++) {
            int v = P->vv[i];
            residual_wt[v] = g->weight[v];
        }

        while ((v=next_vtx_fun(to_colour, numwords))!=-1) {
            copy_bitset(to_colour, candidates, numwords);
            long class_min_wt = residual_wt[v];
            unset_bit(to_colour, v);
            int col_class[MAX_N];
            int col_class_size = 1;
            col_class[0] = v;
            // The next line also removes v from the bitset
            reject_adjacent_vertices(candidates, g->bitadjmat[v], numwords);
            while ((v=next_vtx_fun(candidates, numwords))!=-1) {
                if (residual_wt[v] < class_min_wt) {
                    class_min_wt = residual_wt[v];
                }
                unset_bit(to_colour, v);
                col_class[col_class_size++] = v;
                // The next line also removes v from the bitset
                reject_adjacent_vertices(candidates, g->bitadjmat[v], numwords);
            }
            for (int i=0; i<col_class_size; i++) {
                int w = col_class[i];
                residual_wt[w] -= class_min_wt;
                if (residual_wt[w] > 0) set_bit(to_colour, w);
            }
            total_wt += class_min_wt;
        }
    } else {
        while ((v=next_vtx_fun(to_colour, numwords))!=-1) {
            copy_bitset(to_colour, candidates, numwords);
            long class_max_wt = g->weight[v];
            total_wt += g->weight[v];
            unset_bit(to_colour, v);
            // The next line also removes v from the bitset
            reject_adjacent_vertices(candidates, g->bitadjmat[v], numwords);
            while ((v=next_vtx_fun(candidates, numwords))!=-1) {
                if (g->weight[v] > class_max_wt) {
                    total_wt = total_wt - class_max_wt + g->weight[v];
                    class_max_wt = g->weight[v];
                }
                unset_bit(to_colour, v);
                // The next line also removes v from the bitset
                reject_adjacent_vertices(candidates, g->bitadjmat[v], numwords);
            }
        }
    }
    return total_wt;
}

long vertex_weight_sum(struct Graph *g, struct UnweightedVtxList *P)
{
    long bound = 0;
    for (int i=0; i<P->size; i++)
        bound += g->weight[P->vv[i]];
    return bound;
}

void expand(struct Graph *g, struct VtxList *C, struct UnweightedVtxList *P,
        long *c, struct VtxList *incumbent, int level,
        int (*next_vtx_fun)(unsigned long long *, int), int colouring_type,
        long *expand_call_count)
{
    (*expand_call_count)++;
    if (P->size==0 && C->total_wt>incumbent->total_wt)
        *incumbent = *C;

    long bound = 0;
    switch (colouring_type) {
    case 0:
        bound = C->total_wt + vertex_weight_sum(g, P);
        if (bound <= incumbent->total_wt) return;
        break;
    case 1:
        if (C->total_wt + colouring_bound(g, P, false, next_vtx_fun) <= incumbent->total_wt) return;
        break;
    case 2:
        if (C->total_wt + colouring_bound(g, P, true, next_vtx_fun) <= incumbent->total_wt) return;
        break;
    case 3:
        if (C->total_wt + colouring_bound(g, P, false, next_vtx_fun) <= incumbent->total_wt) return;
        if (C->total_wt + colouring_bound(g, P, true, next_vtx_fun) <= incumbent->total_wt) return;
        break;
    }
    
    struct UnweightedVtxList *new_P = &prealloc.P[level];

    for (int i=P->size-1; i>=0; i--) {
        int v = P->vv[i];
        if (C->total_wt + c[v] <= incumbent->total_wt) return;

        new_P->size = 0;
        for (int j=0; j<i; j++) {
            int w = P->vv[j];
            if (g->adjmat[v][w]) {
                new_P->vv[new_P->size++] = w;
            }
        }

        push_vtx(g, C, v);
        expand(g, C, new_P, c, incumbent, level+1, next_vtx_fun, colouring_type, expand_call_count);
        pop_vtx(g, C);
        if (colouring_type==0) {
            bound -= g->weight[v];
            if (bound <= incumbent->total_wt)
                return;
        }
    }
}

struct VtxList mc(struct Graph* g, long *expand_call_count, bool quiet,
        int colouring_type, int colouring_order, int vtx_ordering)
{
    int vv[MAX_N];
    order_vertices(vv, g, vtx_ordering);

    struct Graph *ordered_graph = induced_subgraph(g, vv, g->n);
    populate_bitadjmat(ordered_graph);

    struct VtxList incumbent = {.size=0, .total_wt=0};

    long *c = malloc(ordered_graph->n * sizeof(*c));

    for (int i=0; i<ordered_graph->n; i++) {
        struct VtxList C = {.size=0, .total_wt=0};
        struct UnweightedVtxList P = {.size=0};
        push_vtx(ordered_graph, &C, i);
        for (int j=0; j<i; j++)
            if (ordered_graph->adjmat[i][j])
                P.vv[P.size++] = j;
        expand(ordered_graph, &C, &P, c, &incumbent, 0, colouring_order ? first_set_bit : last_set_bit,
                colouring_type, expand_call_count);
        c[i] = incumbent.total_wt;
        if (!quiet)
            printf("c[%d]=%ld; Incumbent size: %d\n", i, c[i], incumbent.size);
    }

    // Use vertex indices from original graph
    for (int i=0; i<incumbent.size; i++)
        incumbent.vv[i] = vv[incumbent.vv[i]];

    free(c);
    free_graph(ordered_graph);

    return incumbent;
}
