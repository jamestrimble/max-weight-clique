#define _GNU_SOURCE
#define _POSIX_SOURCE

#include "c_program_timing.h"
#include "graph.h"
#include "sorting.h"
#include "bitset.h"
#include "vertex_ordering.h"
#include "util.h"
#include "colour_order_solver.h"

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*******************************************************************************
*                                     Data                                     *
*******************************************************************************/

/*******************************************************************************
*                                     Stack                                    *
*******************************************************************************/

struct IntStack {
    int *vals;
    int size;
};

void init_IntStack(struct IntStack *s, int capacity)
{
    s->vals = malloc(capacity * sizeof(*s->vals));
    s->size = 0;
}

void clear_IntStack(struct IntStack *s)
{
    s->size = 0;
}

void destroy_IntStack(struct IntStack *s)
{
    free(s->vals);
}

void push(struct IntStack *s, int val)
{
//    assert (s->size < BIGNUM);
    s->vals[s->size++] = val;
}

// prerequisite: the stack has at least one space free
void push_if(struct IntStack *s, int val, bool condition)
{
    s->vals[s->size] = val;
    s->size += condition;
}

int pop(struct IntStack *s)
{
    assert (s->size != 0);
    return s->vals[--s->size];
}

/*******************************************************************************
*******************************************************************************/

struct IntStackWithoutDups {
    int size;
    int *vals;
    bool *on_stack;
};

void init_IntStackWithoutDups(struct IntStackWithoutDups *s,
        int max_member_val)
{
    s->size = 0;
    s->vals = malloc(max_member_val * sizeof(*s->vals));
    s->on_stack = malloc(max_member_val * sizeof(*s->on_stack));
    for (int i=0; i<max_member_val; i++)
        s->on_stack[i] = false;
}

void destroy_IntStackWithoutDups(struct IntStackWithoutDups *s)
{
    free(s->vals);
    free(s->on_stack);
}

void push_without_dups(struct IntStackWithoutDups *s, int val)
{
    if (!s->on_stack[val]) {
//        assert (s->size < BIGNUM);
        s->vals[s->size++] = val;
        s->on_stack[val] = true;
    }
}

int pop_without_dups(struct IntStackWithoutDups *s)
{
    assert (s->size != 0);
    int val = s->vals[--s->size];
    s->on_stack[val] = false;
    return val;
}

void clear_stack_without_dups(struct IntStackWithoutDups *s)
{
    for (int i=0; i<s->size; i++)
        s->on_stack[s->vals[i]] = false;
    s->size = 0;
}

/*******************************************************************************
*******************************************************************************/

struct IntVec
{
    int *vals;
    int size;
    int capacity;
};

void init_IntVec(struct IntVec *vec)
{
    vec->vals = malloc(sizeof(*vec->vals));
    vec->size = 0;
    vec->capacity = 1;
}

void destroy_IntVec(struct IntVec *vec)
{
    free(vec->vals);
}

void clear_IntVec(struct IntVec *vec)
{
    vec->size = 0;
}

void push_to_IntVec(struct IntVec *vec, int val)
{
    if (vec->size == vec->capacity) {
        vec->capacity <<= 1;
        vec->vals = realloc(vec->vals, vec->capacity * sizeof(*vec->vals));
    }
    vec->vals[vec->size++] = val;
}

void pop_from_IntVec(struct IntVec *vec)
{
    --vec->size;
}

/*******************************************************************************
*******************************************************************************/

struct Clause {
    struct IntVec vv;
    long weight;
    long remaining_wt;
    int remaining_vv_count;
};

struct ListOfClauses {
    struct Clause *clause;
    int size;
    int capacity;
};

void init_ListOfClauses(struct ListOfClauses *l, int n)
{
    l->clause = malloc(n * sizeof(*l->clause));
    l->size = 0;
    l->capacity = n;
    for (int i=0; i<n; i++)
    {
        init_IntVec(&l->clause[i].vv);
    }
}

void clear_ListOfClauses(struct ListOfClauses *l)
{
    l->size = 0;
}

void destroy_ListOfClauses(struct ListOfClauses *l)
{
    for (int i=0; i<l->capacity; i++)
    {
        destroy_IntVec(&l->clause[i].vv);
    }
    free(l->clause);
}

/*******************************************************************************
*******************************************************************************/

// Which clauses does each vertex belong to?
struct ClauseMembership {
    struct IntVec *vtx_to_clauses;
    int capacity;
};

void init_ClauseMembership(struct ClauseMembership *cm, int n)
{
    cm->vtx_to_clauses = malloc(n * sizeof(*cm->vtx_to_clauses));
    cm->capacity = n;
    for (int i=0; i<n; i++)
    {
        init_IntVec(&cm->vtx_to_clauses[i]);
    }
}

void destroy_ClauseMembership(struct ClauseMembership *cm)
{
    for (int i=0; i<cm->capacity; i++)
    {
        destroy_IntVec(&cm->vtx_to_clauses[i]);
    }
    free(cm->vtx_to_clauses);
}

/*******************************************************************************
*******************************************************************************/

struct PreAlloc
{
    // in unit_propagate_once, each vertex has a clause index as its reason, or -1
    int *reason;

    // used in unit_propagate_once
    bool *vertex_has_been_propagated;

    // Used in colouring_bound():
    // last_clause[v] is the index of the last clause in which v appears
    int *last_clause;

    unsigned long long *to_colour;

    unsigned long long *candidates;

    unsigned long long *tmp_bitset;

    long *residual_wt;

    int *sorted_vv;

    int *dynamic_antideg;

    struct IntVec unit_clause_indices;

    struct IntStack S;

    struct IntStackWithoutDups I;

    struct IntStackWithoutDups iset;

    struct ListOfClauses cc;

    struct ClauseMembership cm;
};

void init_PreAlloc(struct PreAlloc *pre_alloc, int n)
{
    pre_alloc->reason = malloc(n * sizeof(*pre_alloc->reason));
    pre_alloc->vertex_has_been_propagated = malloc(n * sizeof(*pre_alloc->vertex_has_been_propagated));
    pre_alloc->last_clause = malloc(n * sizeof(*pre_alloc->last_clause));
    pre_alloc->to_colour = malloc((n+BITS_PER_WORD-1)/BITS_PER_WORD * sizeof *pre_alloc->to_colour);
    pre_alloc->candidates = malloc((n+BITS_PER_WORD-1)/BITS_PER_WORD * sizeof *pre_alloc->candidates);
    pre_alloc->tmp_bitset = malloc((n+BITS_PER_WORD-1)/BITS_PER_WORD * sizeof *pre_alloc->tmp_bitset);
    pre_alloc->residual_wt = malloc(n * sizeof *pre_alloc->residual_wt);
    pre_alloc->sorted_vv = malloc(n * sizeof *pre_alloc->sorted_vv);
    pre_alloc->dynamic_antideg = malloc(n * sizeof *pre_alloc->dynamic_antideg);
    init_IntVec(&pre_alloc->unit_clause_indices);
    init_IntStack(&pre_alloc->S, n);
    init_IntStackWithoutDups(&pre_alloc->I, n);
    init_IntStackWithoutDups(&pre_alloc->iset, n);
    init_ListOfClauses(&pre_alloc->cc, n);
    init_ClauseMembership(&pre_alloc->cm, n);
}

void destroy_PreAlloc(struct PreAlloc *pre_alloc)
{
    free(pre_alloc->reason);
    free(pre_alloc->vertex_has_been_propagated);
    free(pre_alloc->last_clause);
    free(pre_alloc->to_colour);
    free(pre_alloc->candidates);
    free(pre_alloc->tmp_bitset);
    free(pre_alloc->residual_wt);
    free(pre_alloc->sorted_vv);
    free(pre_alloc->dynamic_antideg);
    destroy_IntVec(&pre_alloc->unit_clause_indices);
    destroy_IntStack(&pre_alloc->S);
    destroy_IntStackWithoutDups(&pre_alloc->I);
    destroy_IntStackWithoutDups(&pre_alloc->iset);
    destroy_ListOfClauses(&pre_alloc->cc);
    destroy_ClauseMembership(&pre_alloc->cm);
}

/*******************************************************************************
*******************************************************************************/

int get_unique_remaining_vtx(struct Clause *c, int *reason) {
    for (int i=0; i<c->vv.size; i++) {
        int v = c->vv.vals[i];
        if (reason[v] == -1)
            return v;
    }

    assert(false);   // should never reach here
    return -1;
}

void create_inconsistent_set(struct PreAlloc *pre_alloc, struct Graph *g, struct IntStackWithoutDups *I,
        int c_idx, struct ListOfClauses *cc, int *reason)
{
    struct IntStack *S = &pre_alloc->S;
    clear_IntStack(S);
    push(S, c_idx);
    push_without_dups(I, c_idx);
    while(S->size) {
        int d_idx = pop(S);
        struct Clause *d = &cc->clause[d_idx];
        for (int k=0; k<d->vv.size; k++) {
            int t = d->vv.vals[k];
            int r = reason[t];
            if (r != -1) {  // " removed literal l' "
                if (!I->on_stack[r]) {
                    push(S, r);
                    push_without_dups(I, r);
                }
            }
        }
    }
}

void unit_propagate_once(struct PreAlloc *pre_alloc, struct Graph *g, struct ListOfClauses *cc,
        struct IntStackWithoutDups *I)
{
    clear_IntStack(&pre_alloc->S);
    for (int i=0; i<cc->size; i++) {
        struct Clause *clause = &cc->clause[i];
        clause->remaining_vv_count = clause->vv.size;
    }

    for (int i=0; i<pre_alloc->unit_clause_indices.size; i++) {
        int clause_idx = pre_alloc->unit_clause_indices.vals[i];
        if (cc->clause[clause_idx].remaining_wt)
            push(&pre_alloc->S, clause_idx);
    }

    // set reason array to -1 and vertex_has_been_propagated array to 0
    _Static_assert(-1==~0, "Unable to set an array of ints to -1 using memset");
    memset(pre_alloc->reason, -1, g->n * sizeof(int));
    memset(pre_alloc->vertex_has_been_propagated, 0, g->n * sizeof(bool));

    while (pre_alloc->S.size) {
        int u_idx = pop(&pre_alloc->S);
        struct Clause *u = &cc->clause[u_idx];
        assert (u->remaining_vv_count == 1);
        int v = get_unique_remaining_vtx(u, pre_alloc->reason);
        if (!pre_alloc->vertex_has_been_propagated[v]) {
            //TODO: think about the next commented-out line. Should it be included???
            //reason[v] = u_idx;
            for (int i=0; i<g->nonadjlists[v].size; i++) {
                int w = g->nonadjlists[v].vals[i];
                int sz = pre_alloc->cm.vtx_to_clauses[w].size;
                if (sz) {
                    if (pre_alloc->reason[w] == -1) {
                        pre_alloc->reason[w] = u_idx;
                        for (int j=0; j<sz; j++) {
                            int c_idx = pre_alloc->cm.vtx_to_clauses[w].vals[j];
                            struct Clause *c = &cc->clause[c_idx];
                            c->remaining_vv_count--;
                            push_if(&pre_alloc->S, c_idx, c->remaining_vv_count==1);
                            if (c->remaining_vv_count==0) {
                                create_inconsistent_set(pre_alloc, g, I, c_idx, cc, pre_alloc->reason);
                                return;
                            }
                        }
                    }
                }
            }
        }
        pre_alloc->vertex_has_been_propagated[v] = true;
    }
}

void remove_from_clause_membership(int v, int clause_idx, struct ClauseMembership *cm)
{
    for (int i=0; i<cm->vtx_to_clauses[v].size; i++) {
        if (cm->vtx_to_clauses[v].vals[i] == clause_idx) {
            cm->vtx_to_clauses[v].vals[i] = cm->vtx_to_clauses[v].vals[cm->vtx_to_clauses[v].size-1];
            cm->vtx_to_clauses[v].vals[cm->vtx_to_clauses[v].size-1] = clause_idx;
            cm->vtx_to_clauses[v].size--;
            return;
        }
    }
    assert(false);
}

void fake_length_one_clause(struct Clause *clause, int clause_idx, int vtx_pos,
        struct ClauseMembership *cm) {
    int tmp = clause->vv.vals[vtx_pos];
    clause->vv.vals[vtx_pos] = clause->vv.vals[0];
    clause->vv.vals[0] = tmp;
    for (int i=1; i<clause->vv.size; i++) {
        int v = clause->vv.vals[i];
        remove_from_clause_membership(v, clause_idx, cm);
    }
    clause->vv.size = 1;
}

void unfake_length_one_clause(struct Clause *clause, int clause_idx, int clause_len,
        struct ClauseMembership *cm) {
    clause->vv.size = clause_len;
    for (int i=1; i<clause_len; i++) {
        int v = clause->vv.vals[i];
        cm->vtx_to_clauses[v].vals[cm->vtx_to_clauses[v].size++] = clause_idx;
    }
}

bool look_for_iset_using_non_unit_clause(
        struct PreAlloc *pre_alloc,
        struct Graph *g,
        struct Clause *clause,
        int clause_idx,
        struct ListOfClauses *cc)
{
    clear_stack_without_dups(&pre_alloc->iset);
    int clause_len = clause->vv.size;
    for (int z=0; z<clause_len; z++) {
        clear_stack_without_dups(&pre_alloc->I);
        fake_length_one_clause(clause, clause_idx, z, &pre_alloc->cm);
        unit_propagate_once(pre_alloc, g, cc, &pre_alloc->I);
        unfake_length_one_clause(clause, clause_idx, clause_len, &pre_alloc->cm);
        if (pre_alloc->I.size==0)
            return false;
        for (int i=0; i<pre_alloc->I.size; i++)
            push_without_dups(&pre_alloc->iset, pre_alloc->I.vals[i]);
    }
    return true;
}

void remove_clause_membership(struct ClauseMembership *cm, int v, int clause_idx)
{
    for (int i=0; i<cm->vtx_to_clauses[v].size; i++) {
        if (cm->vtx_to_clauses[v].vals[i] == clause_idx) {
            cm->vtx_to_clauses[v].vals[i] = cm->vtx_to_clauses[v].vals[cm->vtx_to_clauses[v].size-1];
            cm->vtx_to_clauses[v].size--;
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
            for (int j=0; j<cc->clause[c_idx].vv.size; j++) {
                int v = cc->clause[c_idx].vv.vals[j];
                remove_clause_membership(cm, v, c_idx);
            }
        }
    }
    cc->clause[max_idx].weight -= min_wt;  // decrease weight of last clause in set
    return min_wt;
}

long unit_propagate(struct PreAlloc *pre_alloc, struct Graph *g, struct ListOfClauses *cc,
        long target_reduction, struct Params *params)
{
    if (params->max_sat_level == 0 || target_reduction <= 0)
        return 0;

    for (int v=0; v<g->n; v++)
        clear_IntVec(&pre_alloc->cm.vtx_to_clauses[v]);

    for (int i=0; i<cc->size; i++) {
        struct Clause *clause = &cc->clause[i];
        for (int j=0; j<clause->vv.size; j++) {
            int v = clause->vv.vals[j];
            push_to_IntVec(&pre_alloc->cm.vtx_to_clauses[v], i);
        }
    }

    clear_IntVec(&pre_alloc->unit_clause_indices);
    for (int i=0; i<cc->size; i++) {
        cc->clause[i].remaining_wt = cc->clause[i].weight;
        if (cc->clause[i].vv.size == 1)
            push_to_IntVec(&pre_alloc->unit_clause_indices, i);
    }

    long improvement = 0;

#ifdef VERY_VERBOSE
    printf("VERY_VERBOSE {\"isets1\": [");
    char *sep = "";
#endif
    for (;;) {
        clear_stack_without_dups(&pre_alloc->I);
        unit_propagate_once(pre_alloc, g, cc, &pre_alloc->I);

        if (pre_alloc->I.size==0)
            break;

        improvement += process_inconsistent_set(&pre_alloc->I, cc, &pre_alloc->cm);
#ifdef VERY_VERBOSE
        printf("%s[", sep);
        sep = ", ";
        char *sep2 = "";
        for (int i=0; i<pre_alloc->I.size; i++) {
            printf("%s%d", sep2, pre_alloc->I.vals[i]);
            sep2 = ", ";
        }
        printf("]");
#endif

        if (improvement >= target_reduction)
            return improvement;
    }
#ifdef VERY_VERBOSE
    printf("]}\n");
#endif

    if (params->max_sat_level == 2) {
#ifdef VERY_VERBOSE
        printf("VERY_VERBOSE {\"isets2\": [");
        sep = "";
#endif
        for (int i=0; i<cc->size; i++) {
            struct Clause *clause = &cc->clause[i];
            for (;;) {
                if (clause->vv.size == 1)
                    break;

                if (clause->remaining_wt == 0)
                    break;

                push_to_IntVec(&pre_alloc->unit_clause_indices, i);

                bool found_iset = look_for_iset_using_non_unit_clause(
                        pre_alloc, g, clause, i, cc);

                pop_from_IntVec(&pre_alloc->unit_clause_indices);

                if (!found_iset)
                    break;

#ifdef VERY_VERBOSE
                printf("%s[", sep);
                sep = ", ";
                char *sep2 = "";
                for (int i=0; i<pre_alloc->iset.size; i++) {
                    printf("%s%d", sep2, pre_alloc->iset.vals[i]);
                    sep2 = ", ";
                }
                printf("]");
#endif
                improvement += process_inconsistent_set(&pre_alloc->iset, cc, &pre_alloc->cm);

                if (improvement >= target_reduction)
                    return improvement;
            }
        }
#ifdef VERY_VERBOSE
        printf("]}\n");
#endif
    }

    return improvement;
}

int choose_best_v(struct PreAlloc *pre_alloc, unsigned long long *candidates,
        int *dynamic_antideg, int numwords)
{
    copy_bitset(candidates, pre_alloc->tmp_bitset, numwords);
    int best_score = INT_MAX;
    int best_v = -1;
    int v;
    while (-1 != (v = first_set_bit(pre_alloc->tmp_bitset, numwords))) {
        int score = pre_alloc->dynamic_antideg[v];
        if (score < best_score) {
            best_v = v;
            best_score = score;
        }
        unset_bit(pre_alloc->tmp_bitset, v);
    }
    return best_v;
}

long do_colouring_with_reordering(struct PreAlloc *pre_alloc, struct Graph *g,
        struct UnweightedVtxList *P, int numwords)
{
    long bound = 0;

    for (int i=0; i<P->size; i++) {
        int v = P->vv[i];
        pre_alloc->sorted_vv[i] = v;
        copy_bitset(pre_alloc->to_colour, pre_alloc->tmp_bitset, numwords);
        bitset_intersect_with(pre_alloc->tmp_bitset, g->bit_complement_nd[v], numwords);
        pre_alloc->dynamic_antideg[v] = bitset_popcount(pre_alloc->tmp_bitset, numwords);
    }
    INSERTION_SORT(int, pre_alloc->sorted_vv, P->size,
            (pre_alloc->dynamic_antideg[pre_alloc->sorted_vv[j-1]] > pre_alloc->dynamic_antideg[pre_alloc->sorted_vv[j]]));

    int k = 0;
    while (!bitset_empty(pre_alloc->to_colour, numwords)) {
        int v;
        while (!test_bit(pre_alloc->to_colour, (v=pre_alloc->sorted_vv[k]))) {
            ++k;
        }

        copy_bitset(pre_alloc->to_colour, pre_alloc->candidates, numwords);
        long class_min_wt = pre_alloc->residual_wt[v];
        unset_bit(pre_alloc->to_colour, v);
        struct Clause *clause = &pre_alloc->cc.clause[pre_alloc->cc.size];
        clause->vv.size = 0;
        push_to_IntVec(&clause->vv, v);
        bitset_intersect_with(pre_alloc->candidates, g->bit_complement_nd[v], numwords);
        while (-1 != (v = choose_best_v(pre_alloc, pre_alloc->candidates, pre_alloc->dynamic_antideg, numwords))) {
            if (pre_alloc->residual_wt[v] < class_min_wt)
                class_min_wt = pre_alloc->residual_wt[v];
            unset_bit(pre_alloc->to_colour, v);
            push_to_IntVec(&clause->vv, v);
            bitset_intersect_with(pre_alloc->candidates, g->bit_complement_nd[v], numwords);
        }
//            printf("%ld\n", class_min_wt);
        for (int i=0; i<clause->vv.size; i++) {
            int w = clause->vv.vals[i];
            pre_alloc->residual_wt[w] -= class_min_wt;
            if (pre_alloc->residual_wt[w] > 0) {
                set_bit(pre_alloc->to_colour, w);
            } else {
                pre_alloc->last_clause[w] = pre_alloc->cc.size;
            }
        }
        bound += class_min_wt;
        clause->weight = class_min_wt;
        pre_alloc->cc.size++;
    }
    return bound;
}

long do_colouring_without_reordering(struct PreAlloc *pre_alloc, struct Graph *g,
        struct UnweightedVtxList *P, int numwords)
{
    long bound = 0;
    int v;
    while ((v=first_set_bit(pre_alloc->to_colour, numwords))!=-1) {
        copy_bitset(pre_alloc->to_colour, pre_alloc->candidates, numwords);
        long class_min_wt = pre_alloc->residual_wt[v];
        unset_bit(pre_alloc->to_colour, v);
        struct Clause *clause = &pre_alloc->cc.clause[pre_alloc->cc.size];
        clause->vv.size = 0;
        push_to_IntVec(&clause->vv, v);
        bitset_intersect_with(pre_alloc->candidates, g->bit_complement_nd[v], numwords);
        while ((v=first_set_bit(pre_alloc->candidates, numwords))!=-1) {
            if (pre_alloc->residual_wt[v] < class_min_wt)
                class_min_wt = pre_alloc->residual_wt[v];
            unset_bit(pre_alloc->to_colour, v);
            push_to_IntVec(&clause->vv, v);
            bitset_intersect_with(pre_alloc->candidates, g->bit_complement_nd[v], numwords);
        }
//            printf("%ld\n", class_min_wt);
        for (int i=0; i<clause->vv.size; i++) {
            int w = clause->vv.vals[i];
            pre_alloc->residual_wt[w] -= class_min_wt;
            if (pre_alloc->residual_wt[w] > 0) {
                set_bit(pre_alloc->to_colour, w);
            } else {
                pre_alloc->last_clause[w] = pre_alloc->cc.size;
            }
        }
        bound += class_min_wt;
        clause->weight = class_min_wt;
        pre_alloc->cc.size++;
    }
    return bound;
}

bool colouring_bound(struct PreAlloc *pre_alloc, struct Graph *g, struct UnweightedVtxList *P,
        long *cumulative_wt_bound, long target, struct Params *params)
{
    for (int i=(g->n+BITS_PER_WORD-1)/BITS_PER_WORD; i--; )
        pre_alloc->to_colour[i] = 0;

    int max_v = 0;
    for (int i=0; i<P->size; i++)
        if (P->vv[i] > max_v)
            max_v = P->vv[i];

    int numwords = max_v/BITS_PER_WORD+1;

    for (int i=0; i<P->size; i++)
        set_bit(pre_alloc->to_colour, P->vv[i]);

    for (int i=0; i<P->size; i++)
        pre_alloc->residual_wt[P->vv[i]] = g->weight[P->vv[i]];

    clear_ListOfClauses(&pre_alloc->cc);

    long bound = params->use_reordering ?
            do_colouring_with_reordering(pre_alloc, g, P, numwords) :
            do_colouring_without_reordering(pre_alloc, g, P, numwords);

#ifdef VERY_VERBOSE
    printf("VERY_VERBOSE {\"clauses\": [");
    char *sep = "";
    long total_wt = 0;
    for (int i=0; i<pre_alloc->cc.size; i++) {
        printf("%s", sep);
        sep = ", ";
        struct Clause *c = &pre_alloc->cc.clause[i];
        printf("{\"weight\": %ld, ", c->weight);
        printf("\"vertices\": [");
        total_wt += c->weight;
        char *sep2 = "";
        for (int j=0; j<c->vv.size; j++) {
            int v = c->vv.vals[j];
            printf("%s%d", sep2, v);
            sep2 = ", ";
        }
        printf("]");
        printf("}");
    }
    printf("], \"total_wt\": %ld}\n", total_wt);
#endif

    long improvement = unit_propagate(pre_alloc, g, &pre_alloc->cc, bound-target, params);

    bool proved_we_can_prune = bound-improvement <= target;

    if (!proved_we_can_prune) {
        P->size = 0;
        bound = 0;
        for (int i=0; i<pre_alloc->cc.size; i++) {
            struct Clause *clause = &pre_alloc->cc.clause[i];
            assert (clause->weight >= 0);
            bound += clause->weight;
            for (int j=0; j<clause->vv.size; j++) {
                int w = clause->vv.vals[j];
                if (pre_alloc->last_clause[w] == i) {
                    cumulative_wt_bound[P->size] = bound;
                    P->vv[P->size++] = w;
                }
            }
        }
    }

    return !proved_we_can_prune;
}

void expand(struct PreAlloc *pre_alloc, struct Graph *g, struct VtxList *C, struct UnweightedVtxList *P,
        struct VtxList *incumbent, long *expand_call_count, struct Params *params)
{
    (*expand_call_count)++;
    if (*expand_call_count % 100000 == 0)
        check_for_timeout();
    if (is_timeout_flag_set()) return;

    if (P->size==0 && C->total_wt>incumbent->total_wt) {
        copy_VtxList(C, incumbent);
        if (!params->quiet)
            printf("New incumbent of weight %ld\n", incumbent->total_wt);
    }

    long *cumulative_wt_bound = malloc(g->n * sizeof *cumulative_wt_bound);

    if (colouring_bound(pre_alloc, g, P, cumulative_wt_bound, incumbent->total_wt - C->total_wt, params)) {
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
            expand(pre_alloc, g, C, &new_P, incumbent, expand_call_count, params);
            vtxlist_pop_vtx(g, C);
        }

        destroy_UnweightedVtxList(&new_P);
    }

    free(cumulative_wt_bound);
}

void mc(struct Graph* g, long *expand_call_count, struct Params params, struct VtxList *incumbent)
{
    calculate_all_degrees(g);

    int *vv = malloc(g->n * sizeof *vv);
    order_vertices(vv, g, params.vtx_ordering);

    struct Graph *ordered_graph = induced_subgraph(g, vv, g->n);
    populate_bit_complement_nd(ordered_graph);
    make_nonadjlists(ordered_graph);

    //////////////
    // check they're correct
    calculate_all_degrees(ordered_graph);
    for (int i=0; i<ordered_graph->n; i++) {
        if (ordered_graph->nonadjlists[i].size != ordered_graph->n - 1 - ordered_graph->degree[i])
            fail("Incorrect nonadj list length");
        for (int j=0; j<ordered_graph->nonadjlists[i].size; j++) {
            if (ordered_graph->adjmat[i][ordered_graph->nonadjlists[i].vals[j]])
                fail("Unexpected edge");
            if (ordered_graph->adjmat[ordered_graph->nonadjlists[i].vals[j]][i])
                fail("Unexpected edge");
        }
    }
    /////////////

    struct UnweightedVtxList P;
    init_UnweightedVtxList(&P, ordered_graph->n);
    for (int v=0; v<g->n; v++) P.vv[P.size++] = v;
    struct VtxList C;
    init_VtxList(&C, ordered_graph->n);

    struct PreAlloc pre_alloc;
    init_PreAlloc(&pre_alloc, g->n);

    expand(&pre_alloc, ordered_graph, &C, &P, incumbent, expand_call_count, &params);

    destroy_PreAlloc(&pre_alloc);

    destroy_VtxList(&C);
    destroy_UnweightedVtxList(&P);

    // Use vertex indices from original graph
    for (int i=0; i<incumbent->size; i++)
        incumbent->vv[i] = vv[incumbent->vv[i]];

    free_graph(ordered_graph);
    free(vv);
}
