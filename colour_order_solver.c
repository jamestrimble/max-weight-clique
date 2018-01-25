#define _GNU_SOURCE
#define _POSIX_SOURCE

#include "c_program_timing.h"
#include "graph.h"
#include "sorting.h"
#include "bitset.h"
#include "vertex_ordering.h"
#include "util.h"
#include "colour_order_solver.h"
#include "data.h"

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

//    fail("Shouldn't have reache30 here in get_unique_remaining_vtx");
    return -1;
}

void create_inconsistent_set(struct IntStackWithoutDups *I, int c_idx,
        struct ListOfClauses *cc, int *reason)
{
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
}

void unit_propagate_once(struct Graph *g, struct ListOfClauses *cc,
        struct ClauseMembership *cm, struct IntStackWithoutDups *I)
{
    struct IntStackWithoutDups S;   // TODO: probably wouldn't have dups anyway?
    fast_init_stack_without_dups(&S, cc->size);
    for (int i=0; i<cc->size; i++) {
        struct Clause *clause = &cc->clause[i];
        if (clause->remaining_wt) {
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
        //printf("S.size %d\n", S.size);
        int u_idx = pop_without_dups(&S);
        struct Clause *u = &cc->clause[u_idx];
//        if (u->remaining_vv_count != 1)
//            fail("Unexpected remaining_vv_count");
        int v = get_unique_remaining_vtx(u, reason);
        //TODO: think about the next commented-out line. Should it be included???
        //reason[v] = u_idx;
        for (int i=0; i<g->nonadjlist_len[v]; i++) {
            int w = g->nonadjlist[v][i];
            if (reason[w] == -1) {
                reason[w] = u_idx;
                for (int j=cm->list_len[w]; j--; ) {
                    int c_idx = cm->list[w][j];
                    struct Clause *c = &cc->clause[c_idx];
                    c->remaining_vv_count--;
                    if (c->remaining_vv_count==1) {
                        push_without_dups(&S, c_idx);
                    } else if (c->remaining_vv_count==0) {
                        create_inconsistent_set(I, c_idx, cc, reason);
                        return;
                    }
                }
            }
        }
    }
}

void remove_clause_membership(struct ClauseMembership *cm, int v, int clause_idx)
{
    for (int i=0; i<cm->list_len[v]; i++) {
        if (cm->list[v][i] == clause_idx) {
            cm->list[v][i] = cm->list[v][cm->list_len[v]-1];
            cm->list_len[v]--;
            return;
        }
    }
}

long unit_propagate(struct Graph *g, struct ListOfClauses *cc, long target_reduction)
{
    static struct ClauseMembership cm;
    fast_ClauseMembership_init(&cm, g->n);
    for (int i=0; i<cc->size; i++) {
        struct Clause *clause = &cc->clause[i];
        for (int j=0; j<clause->vv_len; j++) {
            int v = clause->vv[j];
            cm.list[v][cm.list_len[v]++] = i;
        }
    }
    for (int i=0; i<cc->size; i++)
        cc->clause[i].remaining_wt = cc->clause[i].weight;

    struct IntStackWithoutDups I;

    long retval = 0;

    while (retval < target_reduction) {
        fast_init_stack_without_dups(&I, cc->size);
        unit_propagate_once(g, cc, &cm, &I);

        if (I.size>0) {
            long min_wt = LONG_MAX;
            int max_idx = -1;
            for (int i=0; i<I.size; i++) {
                int c_idx = I.vals[i];
                long wt = cc->clause[c_idx].remaining_wt;
                if (wt < min_wt)
                    min_wt = wt;
                if (c_idx > max_idx)
                    max_idx = c_idx;
            }
            for (int i=0; i<I.size; i++) {
                int c_idx = I.vals[i];
                cc->clause[c_idx].remaining_wt -= min_wt;
                if (cc->clause[c_idx].remaining_wt == 0) {
                    // Remove references to this clause from CM
                    for (int j=0; j<cc->clause[c_idx].vv_len; j++) {
                        int v = cc->clause[c_idx].vv[j];
                        remove_clause_membership(&cm, v, c_idx);
                    }
                }
            }
            //printf("%d\n", max_idx);
            //printf("%ld ", cc->clause[max_idx].weight);
            cc->clause[max_idx].weight -= min_wt;  // decrease weight of last clause in set
            //printf("%ld\n", cc->clause[max_idx].weight);
            retval += min_wt;
        } else {
            break;
        }
    }
    return retval;
}
void colouring_bound(struct Graph *g, struct UnweightedVtxList *P,
        long *cumulative_wt_bound, bool tavares_style, long target)
{
    unsigned long long *to_colour = calloc((g->n+BITS_PER_WORD-1)/BITS_PER_WORD, sizeof *to_colour);
    unsigned long long *candidates = malloc((g->n+BITS_PER_WORD-1)/BITS_PER_WORD * sizeof *candidates);

    int max_v = 0;
    for (int i=0; i<P->size; i++)
        if (P->vv[i] > max_v)
            max_v = P->vv[i];

    int numwords = max_v/BITS_PER_WORD+1;

    for (int i=0; i<P->size; i++)
        set_bit(to_colour, P->vv[i]);

    int v;
    long bound = 0;

    if (tavares_style) {
//        int *col_class = malloc(g->n * sizeof *col_class);
        long *residual_wt = malloc(g->n * sizeof *residual_wt);
        static struct ListOfClauses cc;
        cc.size = 0;
        for (int i=0; i<P->size; i++)
            residual_wt[P->vv[i]] = g->weight[P->vv[i]];

        int last_clause[BIGNUM];  // last_clause[v] is the index of the last
                                  // clause in which v appears
        while ((v=last_set_bit(to_colour, numwords))!=-1) {
            numwords = v/BITS_PER_WORD+1;
            copy_bitset(to_colour, candidates, numwords);
            long class_min_wt = residual_wt[v];
            unset_bit(to_colour, v);
            cc.clause[cc.size].vv_len = 1;
            cc.clause[cc.size].vv[0] = v;
            bitset_intersect_with(candidates, g->bit_complement_nd[v], numwords);
            while ((v=last_set_bit(candidates, v/BITS_PER_WORD+1))!=-1) {
                if (residual_wt[v] < class_min_wt)
                    class_min_wt = residual_wt[v];
                unset_bit(to_colour, v);
                cc.clause[cc.size].vv[cc.clause[cc.size].vv_len++] = v;
                bitset_intersect_with(candidates, g->bit_complement_nd[v], v/BITS_PER_WORD+1);
            }
//            printf("%ld\n", class_min_wt);
            for (int i=0; i<cc.clause[cc.size].vv_len; i++) {
                int w = cc.clause[cc.size].vv[i];
                residual_wt[w] -= class_min_wt;
                if (residual_wt[w] > 0) {
                    set_bit(to_colour, w);
                } else {
                    last_clause[w] = cc.size;
                }
            }
            bound += class_min_wt;
            cc.clause[cc.size].weight = class_min_wt;
            cc.size++;
        }
        if (bound > target)
            unit_propagate(g, &cc, bound-target);

//        long oldbound = bound;
//        printf("%ld ", bound);

        P->size = 0;
        bound = 0;
        for (int i=0; i<cc.size; i++) {
            struct Clause *clause = &cc.clause[i];
            if (clause->weight < 0)
                fail("Unexpectedly low clause weight");
            bound += clause->weight;
//            printf("%ld\n", bound);
            for (int j=0; j<clause->vv_len; j++) {
                int w = clause->vv[j];
                if (last_clause[w] == i) {
                    cumulative_wt_bound[P->size] = bound;
                    P->vv[P->size++] = w;
                }
            }
        }
//        printf("%ld\n", oldbound-bound);
        free(residual_wt);
//        free(col_class);
    } else {
        P->size = 0;
        int j = 0;

        while ((v=last_set_bit(to_colour, numwords))!=-1) {
            numwords = v/BITS_PER_WORD+1;
            copy_bitset(to_colour, candidates, numwords);
            long class_max_wt = g->weight[v];
            unset_bit(to_colour, v);
            P->vv[P->size++] = v;
            bitset_intersect_with(candidates, g->bit_complement_nd[v], numwords);
            while ((v=last_set_bit(candidates, v/BITS_PER_WORD+1))!=-1) {
                if (g->weight[v] > class_max_wt)
                    class_max_wt = g->weight[v];
                unset_bit(to_colour, v);
                P->vv[P->size++] = v;
                bitset_intersect_with(candidates, g->bit_complement_nd[v], v/BITS_PER_WORD+1);
            }
            bound += class_max_wt;
            for (int k=j; k<P->size; k++)
                cumulative_wt_bound[k] = bound;
            j = P->size;
        }
    }
    free(to_colour);
    free(candidates);
}

void expand(struct Graph *g, struct VtxList *C, struct UnweightedVtxList *P,
        struct VtxList *incumbent, int level, long *expand_call_count,
        bool quiet, bool tavares_colour)
{
    (*expand_call_count)++;
    if (*expand_call_count % 100000 == 0)
        check_for_timeout();
    if (is_timeout_flag_set()) return;

    if (!quiet && P->size==0 && C->total_wt>incumbent->total_wt) {
        copy_VtxList(C, incumbent);
        printf("New incumbent of weight %ld\n", incumbent->total_wt);
    }

    long *cumulative_wt_bound = malloc(g->n * sizeof *cumulative_wt_bound);
    colouring_bound(g, P, cumulative_wt_bound, tavares_colour, incumbent->total_wt - C->total_wt);

    struct UnweightedVtxList new_P;
    init_UnweightedVtxList(&new_P, g->n);

    for (int i=P->size-1; i>=0 && C->total_wt+cumulative_wt_bound[i]>incumbent->total_wt; i--) {
        int v = P->vv[i];

        new_P.size = 0;
        for (int j=0; j<i; j++) {
            int w = P->vv[j];
            if (g->adjmat[v][w]) {
                new_P.vv[new_P.size++] = w;
            }
        }

        vtxlist_push_vtx(g, C, v);
        expand(g, C, &new_P, incumbent, level+1, expand_call_count, quiet, tavares_colour);
        vtxlist_pop_vtx(g, C);
    }

    destroy_UnweightedVtxList(&new_P);
    free(cumulative_wt_bound);
}

void mc(struct Graph* g, long *expand_call_count,
        bool quiet, bool tavares_colour, int vtx_ordering, struct VtxList *incumbent)
{
    calculate_all_degrees(g);

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

    struct UnweightedVtxList P;
    init_UnweightedVtxList(&P, ordered_graph->n);
    for (int v=0; v<g->n; v++) P.vv[P.size++] = v;
    struct VtxList C;
    init_VtxList(&C, ordered_graph->n);
    expand(ordered_graph, &C, &P, incumbent, 0, expand_call_count, quiet, tavares_colour);
    destroy_VtxList(&C);
    destroy_UnweightedVtxList(&P);

    // Use vertex indices from original graph
    for (int i=0; i<incumbent->size; i++)
        incumbent->vv[i] = vv[incumbent->vv[i]];

    free_graph(ordered_graph);
    free(vv);
}
