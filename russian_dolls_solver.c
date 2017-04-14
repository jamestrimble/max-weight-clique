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

// Returns an upper bound on weight from the vertices in P
bool can_prune_by_colouring(struct Graph *g, struct UnweightedVtxList *P, bool tavares_style,
        int (*next_vtx_fun)(unsigned long long *, int), long K)
{
    unsigned long long *to_colour = calloc((g->n+BITS_PER_WORD-1)/BITS_PER_WORD, sizeof *to_colour);
    unsigned long long *candidates = malloc((g->n+BITS_PER_WORD-1)/BITS_PER_WORD * sizeof *candidates);

    if (P->size==0) return K >= 0;

    int max_v = P->vv[P->size-1];
    int numwords = max_v/BITS_PER_WORD+1;

    for (int i=0; i<P->size; i++)
        set_bit(to_colour, P->vv[i]);

    int v;

    if (tavares_style) {
        int *col_class = malloc(g->n * sizeof *col_class);
        long *residual_wt = malloc(g->n * sizeof *residual_wt);
        for (int i=0; i<P->size; i++) {
            int v = P->vv[i];
            residual_wt[v] = g->weight[v];
        }

        while ((v=next_vtx_fun(to_colour, numwords))!=-1) {
            copy_bitset(to_colour, candidates, numwords);
            long class_min_wt = residual_wt[v];
            unset_bit(to_colour, v);
            int col_class_size = 1;
            col_class[0] = v;
            bitset_intersect_with(candidates, g->bit_complement_nd[v], numwords);
            while ((v=next_vtx_fun(candidates, numwords))!=-1) {
                if (residual_wt[v] < class_min_wt) {
                    class_min_wt = residual_wt[v];
                }
                unset_bit(to_colour, v);
                col_class[col_class_size++] = v;
                bitset_intersect_with(candidates, g->bit_complement_nd[v], numwords);
            }
            for (int i=0; i<col_class_size; i++) {
                int w = col_class[i];
                residual_wt[w] -= class_min_wt;
                if (residual_wt[w] > 0) set_bit(to_colour, w);
            }
            K -= class_min_wt;
            if (K < 0) break;
        }
        free(residual_wt);
        free(col_class);
    } else {
        while ((v=next_vtx_fun(to_colour, numwords))!=-1) {
            copy_bitset(to_colour, candidates, numwords);
            long class_max_wt = g->weight[v];
            K -= g->weight[v];
            unset_bit(to_colour, v);
            bitset_intersect_with(candidates, g->bit_complement_nd[v], numwords);
            while ((v=next_vtx_fun(candidates, numwords))!=-1) {
                if (g->weight[v] > class_max_wt) {
                    K = K + class_max_wt - g->weight[v];
                    class_max_wt = g->weight[v];
                }
                unset_bit(to_colour, v);
                bitset_intersect_with(candidates, g->bit_complement_nd[v], numwords);
            }
            if (K < 0) break;
        }
    }
    free(to_colour);
    free(candidates);
    return K >= 0;
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
    if (*expand_call_count % 100000 == 0)
        check_for_timeout();
    if (is_timeout_flag_set()) return;

    if (P->size==0 && C->total_wt>incumbent->total_wt)
        copy_VtxList(C, incumbent);

    long bound = 0;
    switch (colouring_type) {
    case 0:
        bound = C->total_wt + vertex_weight_sum(g, P);
        if (bound <= incumbent->total_wt) return;
        break;
    case 1:
        if (can_prune_by_colouring(g, P, false, next_vtx_fun, incumbent->total_wt-C->total_wt)) return;
        break;
    case 2:
        if (can_prune_by_colouring(g, P, true, next_vtx_fun, incumbent->total_wt-C->total_wt)) return;
        break;
    case 3:
        if (can_prune_by_colouring(g, P, false, next_vtx_fun, incumbent->total_wt-C->total_wt)) return;
        if (can_prune_by_colouring(g, P, true, next_vtx_fun, incumbent->total_wt-C->total_wt)) return;
        break;
    }
    
    struct UnweightedVtxList new_P;
    init_UnweightedVtxList(&new_P, g->n);

    for (int i=P->size-1; i>=0; i--) {
        int v = P->vv[i];
        if (C->total_wt + c[v] <= incumbent->total_wt) break;

        new_P.size = 0;
        for (int j=0; j<i; j++) {
            int w = P->vv[j];
            if (g->adjmat[v][w]) {
                new_P.vv[new_P.size++] = w;
            }
        }

        vtxlist_push_vtx(g, C, v);
        expand(g, C, &new_P, c, incumbent, level+1, next_vtx_fun, colouring_type, expand_call_count);
        vtxlist_pop_vtx(g, C);
        if (colouring_type==0) {
            bound -= g->weight[v];
            if (bound <= incumbent->total_wt)
                break;
        }
    }

    destroy_UnweightedVtxList(&new_P);
}

void mc(struct Graph* g, long *expand_call_count, bool quiet,
        int colouring_type, int colouring_order, int vtx_ordering, struct VtxList *incumbent)
{
    int *vv = malloc(g->n * sizeof *vv);
    order_vertices(vv, g, vtx_ordering);

    struct Graph *ordered_graph = induced_subgraph(g, vv, g->n);
    populate_bit_complement_nd(ordered_graph);

    long *c = malloc(ordered_graph->n * sizeof(*c));

    for (int i=0; i<ordered_graph->n; i++) {
        if (is_timeout_flag_set()) break;
        struct VtxList C;
        init_VtxList(&C, ordered_graph->n);
        struct UnweightedVtxList P;
        init_UnweightedVtxList(&P, ordered_graph->n);
        vtxlist_push_vtx(ordered_graph, &C, i);
        for (int j=0; j<i; j++)
            if (ordered_graph->adjmat[i][j])
                P.vv[P.size++] = j;
        expand(ordered_graph, &C, &P, c, incumbent, 0, colouring_order ? first_set_bit : last_set_bit,
                colouring_type, expand_call_count);
        c[i] = incumbent->total_wt;
        if (!quiet)
            printf("c[%d]=%ld; Incumbent size: %d\n", i, c[i], incumbent->size);
        destroy_VtxList(&C);
        destroy_UnweightedVtxList(&P);
    }

    // Use vertex indices from original graph
    for (int i=0; i<incumbent->size; i++)
        incumbent->vv[i] = vv[incumbent->vv[i]];

    free(c);
    free_graph(ordered_graph);
    free(vv);
}
