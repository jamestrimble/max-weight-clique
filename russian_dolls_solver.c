#define _GNU_SOURCE
#define _POSIX_SOURCE

#include "c_program_timing.h"
#include "data.h"
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

int get_unique_remaining_vtx(struct Clause *c, int *reason) {
    for (int i=0; i<c->vv_len; i++) {
        int v = c->vv[i];
        if (reason[v] == -1)
            return v;
    }

    fail("Shouldn't have reache30 here in get_unique_remaining_vtx");
    return -1;
}

void unit_propagate_once(struct Graph *g, struct ListOfClauses *cc,
        struct ClauseMembership *cm, struct IntStackWithoutDups *I)
{
    struct IntStackWithoutDups S;   // TODO: probably wouldn't have dups anyway?
    init_stack_without_dups(&S);
    for (int i=0; i<cc->size; i++) {
        struct Clause *clause = &cc->clause[i];
        if (!clause->used) {
            clause->remaining_vv_count = clause->vv_len;
            if (clause->vv_len==1) {
                push_without_dups(&S, i);
            }
        }
    }
//    INSERTION_SORT(int, S.vals, S.size,
//            (cc->clause[S.vals[j-1]].weight > cc->clause[S.vals[j]].weight))

    // each vertex has a clause index as its reason, or -1
    int reason[BIGNUM];
    for (int i=0; i<g->n; i++)
        reason[i] = -1;

    while (S.size) {
        int u_idx = pop_without_dups(&S);
        struct Clause *u = &cc->clause[u_idx];
        if (u->remaining_vv_count != 1)
            fail("Unexpected remaining_vv_count");
        int v = get_unique_remaining_vtx(u, reason);
        //TODO: think about the next commented-out line. Should it be included???
        //reason[v] = u_idx;
        for (int i=0; i<g->nonadjlist_len[v]; i++) {
            int w = g->nonadjlist[v][i];
            if (reason[w] == -1) {
                reason[w] = u_idx;
                for (int j=0; j<cm->list_len[w]; j++) {
                    int c_idx = cm->list[w][j];
                    struct Clause *c = &cc->clause[c_idx];
                    c->remaining_vv_count--;
                    if (c->remaining_vv_count==1) {
                        push_without_dups(&S, c_idx);
                    } else if (c->remaining_vv_count==0) {
                        //printf("yay!\n");
                        struct IntQueue Q;
                        init_queue(&Q);
                        enqueue(&Q, c_idx);
                        push_without_dups(I, c_idx);
                        while(!queue_empty(&Q)) {
                            int d_idx = dequeue(&Q);
                            struct Clause *d = &cc->clause[d_idx];
                            for (int k=0; k<d->vv_len; k++) {
                                int t = d->vv[k];
                                int r = reason[t];
                                if (r != -1) {  // " removed literal l' "
                                    if (!I->on_stack[r]) {
                                        enqueue(&Q, r);
                                        push_without_dups(I, r);
                                    }
                                }
                            }
                        }
                        return;
                    }
                }
            }
        }
    }
}

void remove_clause_membership(struct ClauseMembership *cm, int v, int clause_idx)
{
    // TODO: make this more efficient when you're sure it works
    int pos = -1;
    for (int i=0; i<cm->list_len[v]; i++) {
        if (cm->list[v][i] == clause_idx) {
            pos = i;
            break;
        }
    }
    if (pos==-1)
        fail("Couldn't find clause in membership list");
    int tmp = cm->list[v][cm->list_len[v]-1];
    cm->list[v][cm->list_len[v]-1] = cm->list[v][pos];
    cm->list[v][pos] = tmp;
    cm->list_len[v]--;
}

long unit_propagate(struct Graph *g, struct ListOfClauses *cc, long target_reduction)
{
    static struct ClauseMembership cm;
    ClauseMembership_init(&cm);
    for (int i=0; i<cc->size; i++) {
        struct Clause *clause = &cc->clause[i];
        for (int j=0; j<clause->vv_len; j++) {
            int v = clause->vv[j];
            cm.list[v][cm.list_len[v]++] = i;
        }
    }
    for (int i=0; i<cc->size; i++)
        cc->clause[i].used = false;

    struct IntStackWithoutDups I;

    long retval = 0;

    while (retval < target_reduction) {
        init_stack_without_dups(&I);
        unit_propagate_once(g, cc, &cm, &I);

        if (I.size>0) {
            long min_wt = LONG_MAX;
            for (int i=0; i<I.size; i++) {
                int c_idx = I.vals[i];
                cc->clause[c_idx].used = true;
                long wt = cc->clause[c_idx].weight;
                if (wt < min_wt)
                    min_wt = wt;
                // Remove references to this clause from CM
                for (int j=0; j<cc->clause[c_idx].vv_len; j++) {
                    int v = cc->clause[c_idx].vv[j];
                    remove_clause_membership(&cm, v, c_idx);
                }
            }
            retval += min_wt;
            // TODO: update cm
        } else {
            break;
        }
//        break;  // TODO: don't break!
    }
    return retval;
}

// Returns an upper bound on weight from the vertices in P
long colouring_bound(struct Graph *g, struct UnweightedVtxList *P, bool tavares_style,
        int (*next_vtx_fun)(unsigned long long *, int), bool use_unitprop, long target)
{
    unsigned long long *to_colour = calloc((g->n+BITS_PER_WORD-1)/BITS_PER_WORD, sizeof *to_colour);
    unsigned long long *candidates = malloc((g->n+BITS_PER_WORD-1)/BITS_PER_WORD * sizeof *candidates);

    if (P->size==0) return 0;

    int max_v = P->vv[P->size-1];
    int numwords = max_v/BITS_PER_WORD+1;

    for (int i=0; i<P->size; i++)
        set_bit(to_colour, P->vv[i]);

    int v;
    long total_wt = 0;

    if (tavares_style) {
//        int *col_class = malloc(g->n * sizeof *col_class);
        long *residual_wt = malloc(g->n * sizeof *residual_wt);
        static struct ListOfClauses cc;
        cc.size = 0;
        for (int i=0; i<P->size; i++) {
            int v = P->vv[i];
            residual_wt[v] = g->weight[v];
        }

        while ((v=next_vtx_fun(to_colour, numwords))!=-1) {
            copy_bitset(to_colour, candidates, numwords);
            long class_min_wt = residual_wt[v];
            unset_bit(to_colour, v);
            cc.clause[cc.size].vv_len = 1;
            cc.clause[cc.size].vv[0] = v;
            bitset_intersect_with(candidates, g->bit_complement_nd[v], numwords);
            while ((v=next_vtx_fun(candidates, numwords))!=-1) {
                if (residual_wt[v] < class_min_wt) {
                    class_min_wt = residual_wt[v];
                }
                unset_bit(to_colour, v);
                cc.clause[cc.size].vv[cc.clause[cc.size].vv_len++] = v;
                bitset_intersect_with(candidates, g->bit_complement_nd[v], numwords);
            }
            for (int i=0; i<cc.clause[cc.size].vv_len; i++) {
                int w = cc.clause[cc.size].vv[i];
                residual_wt[w] -= class_min_wt;
                if (residual_wt[w] > 0) set_bit(to_colour, w);
            }
            cc.clause[cc.size].weight = class_min_wt;
            total_wt += class_min_wt;
            cc.size++;
        }
        if (use_unitprop && total_wt > target)
            total_wt -= unit_propagate(g, &cc, total_wt - target);
        free(residual_wt);
//        free(col_class);
    } else {
        while ((v=next_vtx_fun(to_colour, numwords))!=-1) {
            copy_bitset(to_colour, candidates, numwords);
            long class_max_wt = g->weight[v];
            total_wt += g->weight[v];
            unset_bit(to_colour, v);
            bitset_intersect_with(candidates, g->bit_complement_nd[v], numwords);
            while ((v=next_vtx_fun(candidates, numwords))!=-1) {
                if (g->weight[v] > class_max_wt) {
                    total_wt = total_wt - class_max_wt + g->weight[v];
                    class_max_wt = g->weight[v];
                }
                unset_bit(to_colour, v);
                bitset_intersect_with(candidates, g->bit_complement_nd[v], numwords);
            }
        }
    }
    free(to_colour);
    free(candidates);
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
        if (C->total_wt + colouring_bound(g, P, false, next_vtx_fun, false, incumbent->total_wt - C->total_wt) <= incumbent->total_wt) return;
        break;
    case 2:
        //if (C->total_wt + colouring_bound(g, P, true, next_vtx_fun, false, incumbent->total_wt - C->total_wt) <= incumbent->total_wt) return;
        if (C->total_wt + colouring_bound(g, P, true, next_vtx_fun, true, incumbent->total_wt - C->total_wt) <= incumbent->total_wt) return;
        break;
    case 3:
        if (C->total_wt + colouring_bound(g, P, false, next_vtx_fun, false, incumbent->total_wt - C->total_wt) <= incumbent->total_wt) return;
        //if (C->total_wt + colouring_bound(g, P, true, next_vtx_fun, false, incumbent->total_wt - C->total_wt) <= incumbent->total_wt) return;
        if (C->total_wt + colouring_bound(g, P, true, next_vtx_fun, true, incumbent->total_wt - C->total_wt) <= incumbent->total_wt) return;
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
    make_nonadjlists(ordered_graph);

    //////////////
    // check they're correct
    calculate_all_degrees(ordered_graph);
    for (int i=0; i<ordered_graph->n; i++) {
        if (ordered_graph->nonadjlist_len[i] != ordered_graph->n - 1 - ordered_graph->degree[i])
            fail("Incorrect nonadj list length");
        for (int j=0; j<ordered_graph->nonadjlist_len[i]; j++) {
            if (ordered_graph->adjmat[i][ordered_graph->nonadjlist[i][j]])
                fail("Unexpected edge");
            if (ordered_graph->adjmat[ordered_graph->nonadjlist[i][j]][i])
                fail("Unexpected edge");
        }
    }
    /////////////

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
