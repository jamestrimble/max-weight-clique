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
#include <string.h>

#define MIN(X, Y) (((X) < (Y)) ? (X) : (Y))

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

void expand(struct VtxList *C, struct UnweightedVtxList *P, struct VtxList *incumbent, int level,
        long *expand_call_count, bool quiet, bool tavares_colour)
{
    (*expand_call_count)++;
    if (!quiet && P->size==0 && C->total_wt>incumbent->total_wt) {
        *incumbent = *C;
        printf("New incumbent of weight %ld\n", incumbent->total_wt);
    }

    long cumulative_wt_bound[MAX_N];

    if (tavares_colour)
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
        expand(C, new_P, incumbent, level+1, expand_call_count, quiet, tavares_colour);
        pop_vtx(C);
    }
}

struct VtxList mc(struct Graph* g, long *expand_call_count,
        bool quiet, bool tavares_colour, int vtx_ordering)
{
    calculate_all_degrees(g);

    int vv[MAX_N];
    order_vertices(vv, g, vtx_ordering);

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
    expand(&C, &P, &incumbent, 0, expand_call_count, quiet, tavares_colour);

    // Use vertex indices from original graph
    for (int i=0; i<incumbent.size; i++)
        incumbent.vv[i] = vv[incumbent.vv[i]];

    return incumbent;
}
