#define _GNU_SOURCE
#define _POSIX_SOURCE

#include "c_program_timing.h"
#include "graph.h"
#include "sorting.h"
#include "bitset.h"
#include "vertex_ordering.h"
#include "util.h"
#include "colour_order_solver.h"

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void colouring_bound(struct Graph *g, struct UnweightedVtxList *P,
        long *cumulative_wt_bound, bool tavares_style)
{
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

    int v;
    long bound = 0;

    if (tavares_style) {
        int *col_class = malloc(g->n * sizeof *col_class);
        long *residual_wt = malloc(g->n * sizeof *residual_wt);
        for (int i=0; i<P->size; i++)
            residual_wt[P->vv[i]] = g->weight[P->vv[i]];

        P->size = 0;

        while ((v=last_set_bit(to_colour, numwords))!=-1) {
            numwords = v/BITS_PER_WORD+1;
            copy_bitset(to_colour, candidates, numwords);
            long class_min_wt = residual_wt[v];
            unset_bit(to_colour, v);
            int col_class_size = 1;
            col_class[0] = v;
            // The next line also removes v from the bitset
            reject_adjacent_vertices(candidates, g->bitadjmat[v], numwords);
            while ((v=last_set_bit(candidates, v/BITS_PER_WORD+1))!=-1) {
                if (residual_wt[v] < class_min_wt)
                    class_min_wt = residual_wt[v];
                unset_bit(to_colour, v);
                col_class[col_class_size++] = v;
                // The next line also removes v from the bitset
                reject_adjacent_vertices(candidates, g->bitadjmat[v], v/BITS_PER_WORD+1);
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
        free(residual_wt);
        free(col_class);
    } else {
        P->size = 0;
        int j = 0;

        while ((v=last_set_bit(to_colour, numwords))!=-1) {
            numwords = v/BITS_PER_WORD+1;
            copy_bitset(to_colour, candidates, numwords);
            long class_max_wt = g->weight[v];
            unset_bit(to_colour, v);
            P->vv[P->size++] = v;
            // The next line also removes v from the bitset
            reject_adjacent_vertices(candidates, g->bitadjmat[v], numwords);
            while ((v=last_set_bit(candidates, v/BITS_PER_WORD+1))!=-1) {
                if (g->weight[v] > class_max_wt)
                    class_max_wt = g->weight[v];
                unset_bit(to_colour, v);
                P->vv[P->size++] = v;
                // The next line also removes v from the bitset
                reject_adjacent_vertices(candidates, g->bitadjmat[v], v/BITS_PER_WORD+1);
            }
            bound += class_max_wt;
            for (int k=j; k<P->size; k++)
                cumulative_wt_bound[k] = bound;
            j = P->size;
        }
    }
}

void expand(struct Graph *g, struct VtxList *C, struct UnweightedVtxList *P,
        struct VtxList *incumbent, int level, long *expand_call_count,
        bool quiet, bool tavares_colour)
{
    (*expand_call_count)++;
    if (!quiet && P->size==0 && C->total_wt>incumbent->total_wt) {
        *incumbent = *C;
        printf("New incumbent of weight %ld\n", incumbent->total_wt);
    }

    long *cumulative_wt_bound = malloc(g->n * sizeof *cumulative_wt_bound);
    colouring_bound(g, P, cumulative_wt_bound, tavares_colour);

    struct UnweightedVtxList *new_P = malloc(sizeof *new_P);

    for (int i=P->size-1; i>=0 && C->total_wt+cumulative_wt_bound[i]>incumbent->total_wt; i--) {
        int v = P->vv[i];

        new_P->size = 0;
        for (int j=0; j<i; j++) {
            int w = P->vv[j];
            if (g->adjmat[v][w]) {
                new_P->vv[new_P->size++] = w;
            }
        }

        vtxlist_push_vtx(g, C, v);
        expand(g, C, new_P, incumbent, level+1, expand_call_count, quiet, tavares_colour);
        vtxlist_pop_vtx(g, C);
    }

    free(new_P);
    free(cumulative_wt_bound);
}

struct VtxList mc(struct Graph* g, long *expand_call_count,
        bool quiet, bool tavares_colour, int vtx_ordering)
{
    calculate_all_degrees(g);

    int *vv = malloc(g->n * sizeof *vv);
    order_vertices(vv, g, vtx_ordering);

    struct Graph *ordered_graph = induced_subgraph(g, vv, g->n);
    populate_bitadjmat(ordered_graph);

    struct VtxList incumbent = {.size=0, .total_wt=0};

    struct UnweightedVtxList P = {.size=0};
    for (int v=0; v<g->n; v++) P.vv[P.size++] = v;
    struct VtxList C = {.size=0, .total_wt=0};
    expand(ordered_graph, &C, &P, &incumbent, 0, expand_call_count, quiet, tavares_colour);

    // Use vertex indices from original graph
    for (int i=0; i<incumbent.size; i++)
        incumbent.vv[i] = vv[incumbent.vv[i]];

    free_graph(ordered_graph);
    free(vv);

    return incumbent;
}
