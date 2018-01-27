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
    struct IntStack S;
    init_stack(&S);
    for (int i=0; i<cc->size; i++) {
        struct Clause *clause = &cc->clause[i];
        if (clause->remaining_wt) {
            clause->remaining_vv_count = clause->vv_len;
            if (clause->vv_len==1) {
                push(&S, i);
            }
        }
    }
//    INSERTION_SORT(int, S.vals, S.size,
//            (cc->clause[S.vals[j-1]].weight > cc->clause[S.vals[j]].weight))

    // each vertex has a clause index as its reason, or -1
    int reason[BIGNUM];
    bool vertex_has_been_propagated[BIGNUM];
    for (int i=0; i<g->n; i++) {
        reason[i] = -1;
        vertex_has_been_propagated[i] = false;
    }

    while (S.size) {
        //printf("S.size %d\n", S.size);
        int u_idx = pop(&S);
        struct Clause *u = &cc->clause[u_idx];
//        if (u->remaining_vv_count != 1)
//            fail("Unexpected remaining_vv_count");
        int v = get_unique_remaining_vtx(u, reason);
        if (!vertex_has_been_propagated[v]) {
//            printf("%d ", v);
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
                            push(&S, c_idx);
                        } else if (c->remaining_vv_count==0) {
                            create_inconsistent_set(I, c_idx, cc, reason);
//                            printf("\n");
                            return;
                        }
                    }
                }
            }
        }
        vertex_has_been_propagated[v] = true;
    }
//    printf("\n");
}

void remove_from_clause_membership(int v, int clause_idx, struct ClauseMembership *cm)
{
    for (int i=0; i<cm->list_len[v]; i++) {
        if (cm->list[v][i] == clause_idx) {
            cm->list[v][i] = cm->list[v][cm->list_len[v]-1];
            cm->list[v][cm->list_len[v]-1] = clause_idx;
            cm->list_len[v]--;
            return;
        }
    }
    fail("fell off the end of remove_from_clause_membership\n");
}

void fake_length_one_clause(struct Clause *clause, int clause_idx, int vtx_pos,
        struct ClauseMembership *cm) {
    int tmp = clause->vv[vtx_pos];
    clause->vv[vtx_pos] = clause->vv[0];
    clause->vv[0] = tmp;
    for (int i=1; i<clause->vv_len; i++) {
        int v = clause->vv[i];
        remove_from_clause_membership(v, clause_idx, cm);
    }
    clause->vv_len = 1;
}

void unfake_length_one_clause(struct Clause *clause, int clause_idx, int clause_len,
        struct ClauseMembership *cm) {
    clause->vv_len = clause_len;
    for (int i=1; i<clause_len; i++) {
        int v = clause->vv[i];
        cm->list[v][cm->list_len[v]++] = clause_idx;
    }
}

bool look_for_iset_using_non_unit_clause(
        struct Graph *g,
        struct Clause *clause,
        int clause_idx,
        struct ListOfClauses *cc,
        struct ClauseMembership *cm,
        struct IntStackWithoutDups *I,
        struct IntStackWithoutDups *iset)
{
    clear_stack_without_dups(iset);
    int clause_len = clause->vv_len;
    for (int z=0; z<clause_len; z++) {
        clear_stack_without_dups(I);
        fake_length_one_clause(clause, clause_idx, z, cm);
        unit_propagate_once(g, cc, cm, I);
        unfake_length_one_clause(clause, clause_idx, clause_len, cm);
        if (I->size==0)
            return false;
        for (int i=0; i<I->size; i++)
            push_without_dups(iset, I->vals[i]);
    }
    return true;
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

long process_inconsistent_set(
        struct IntStackWithoutDups *iset,
        struct ListOfClauses *cc,
        struct ClauseMembership *cm)
{
    if (iset->size == 0)
        return 0;

    long min_wt = LONG_MAX;
    int max_idx = -1;
    for (int i=0; i<iset->size; i++) {
        int c_idx = iset->vals[i];
        long wt = cc->clause[c_idx].remaining_wt;
        if (wt < min_wt)
            min_wt = wt;
        if (c_idx > max_idx)
            max_idx = c_idx;
    }
    for (int i=0; i<iset->size; i++) {
        int c_idx = iset->vals[i];
        cc->clause[c_idx].remaining_wt -= min_wt;
        if (cc->clause[c_idx].remaining_wt == 0) {
            // Remove references to this clause from CM
            for (int j=0; j<cc->clause[c_idx].vv_len; j++) {
                int v = cc->clause[c_idx].vv[j];
                remove_clause_membership(cm, v, c_idx);
            }
        }
    }
    cc->clause[max_idx].weight -= min_wt;  // decrease weight of last clause in set
    return min_wt;
}

long unit_propagate(struct Graph *g, struct ListOfClauses *cc, long target_reduction)
{
    if (target_reduction <= 0)
        return 0;

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
    fast_init_stack_without_dups(&I, cc->size);

    long improvement = 0;

    for (;;) {
        clear_stack_without_dups(&I);
        unit_propagate_once(g, cc, &cm, &I);

        if (I.size==0)
            break;

        improvement += process_inconsistent_set(&I, cc, &cm);

        if (improvement >= target_reduction)
            return improvement;
    }

//    for (int i=0; i<cc->size; i++) {
//        struct Clause *clause = &cc->clause[i];
//        printf("%ld ", clause->remaining_wt);
//    }
//    printf("\n");
//    printf("\n");
//
    struct IntStackWithoutDups iset;
    fast_init_stack_without_dups(&iset, cc->size);
    for (int i=0; i<cc->size; i++) {
        struct Clause *clause = &cc->clause[i];
        for (;;) {
            if (clause->vv_len == 1)
                break;

            if (clause->remaining_wt == 0)
                break;

            bool found_iset = look_for_iset_using_non_unit_clause(
                    g, clause, i, cc, &cm, &I, &iset);

            if (!found_iset)
                break;

            improvement += process_inconsistent_set(&iset, cc, &cm);

            if (improvement >= target_reduction)
                return improvement;
        }
    }

    return improvement;
}

bool colouring_bound(struct Graph *g, struct UnweightedVtxList *P,
        long *cumulative_wt_bound, long target)
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

    long *residual_wt = malloc(g->n * sizeof *residual_wt);
    static struct ListOfClauses cc;
    cc.size = 0;
    for (int i=0; i<P->size; i++)
        residual_wt[P->vv[i]] = g->weight[P->vv[i]];

    int last_clause[BIGNUM];  // last_clause[v] is the index of the last
                              // clause in which v appears
    while ((v=first_set_bit(to_colour, numwords))!=-1) {
//            numwords = v/BITS_PER_WORD+1;
        copy_bitset(to_colour, candidates, numwords);
        long class_min_wt = residual_wt[v];
        unset_bit(to_colour, v);
        struct Clause *clause = &cc.clause[cc.size];
        clause->vv_len = 1;
        clause->vv[0] = v;
        bitset_intersect_with(candidates, g->bit_complement_nd[v], numwords);
        while ((v=first_set_bit(candidates, numwords))!=-1) {
            if (residual_wt[v] < class_min_wt)
                class_min_wt = residual_wt[v];
            unset_bit(to_colour, v);
            clause->vv[clause->vv_len++] = v;
            bitset_intersect_with(candidates, g->bit_complement_nd[v], numwords);
        }
//            printf("%ld\n", class_min_wt);
        for (int i=0; i<clause->vv_len; i++) {
            int w = clause->vv[i];
            residual_wt[w] -= class_min_wt;
            if (residual_wt[w] > 0) {
                set_bit(to_colour, w);
            } else {
                last_clause[w] = cc.size;
            }
        }
        bound += class_min_wt;
        clause->weight = class_min_wt;
        cc.size++;
    }

    long improvement = unit_propagate(g, &cc, bound-target);

    bool proved_we_can_prune = bound-improvement <= target;

    if (!proved_we_can_prune) {
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
    }

    free(residual_wt);
    free(to_colour);
    free(candidates);

    return !proved_we_can_prune;
}

void expand(struct Graph *g, struct VtxList *C, struct UnweightedVtxList *P,
        struct VtxList *incumbent, int level, long *expand_call_count,
        bool quiet)
{
    (*expand_call_count)++;
    if (*expand_call_count % 100000 == 0)
        check_for_timeout();
    if (is_timeout_flag_set()) return;

    if (P->size==0 && C->total_wt>incumbent->total_wt) {
        copy_VtxList(C, incumbent);
        if (!quiet)
            printf("New incumbent of weight %ld\n", incumbent->total_wt);
    }

    long *cumulative_wt_bound = malloc(g->n * sizeof *cumulative_wt_bound);

    if (colouring_bound(g, P, cumulative_wt_bound, incumbent->total_wt - C->total_wt)) {
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
            expand(g, C, &new_P, incumbent, level+1, expand_call_count, quiet);
            vtxlist_pop_vtx(g, C);
        }

        destroy_UnweightedVtxList(&new_P);
    }

    free(cumulative_wt_bound);
}

void mc(struct Graph* g, long *expand_call_count,
        bool quiet, int vtx_ordering, struct VtxList *incumbent)
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
    expand(ordered_graph, &C, &P, incumbent, 0, expand_call_count, quiet);
    destroy_VtxList(&C);
    destroy_UnweightedVtxList(&P);

    // Use vertex indices from original graph
    for (int i=0; i<incumbent->size; i++)
        incumbent->vv[i] = vv[incumbent->vv[i]];

    free_graph(ordered_graph);
    free(vv);
}
