#define _GNU_SOURCE
#define _POSIX_SOURCE

#include "c_program_timing.h"
#include "graph.h"
#include "sorting.h"
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
*                                    Bitsets                                   *
*******************************************************************************/

void set_bit(unsigned long long *bitset, int bit)
{
    bitset[bit/BITS_PER_WORD] |= (1ull << (bit%BITS_PER_WORD));
}

void unset_bit(unsigned long long *bitset, int bit)
{
    bitset[bit/BITS_PER_WORD] &= ~(1ull << (bit%BITS_PER_WORD));
}

bool bitset_empty(unsigned long long *bitset, int num_words)
{
    for (int i=0; i<num_words; i++)
        if (bitset[i] != 0)
            return false;
    return true;
}

int first_set_bit(unsigned long long *bitset,
                         int num_words)
{
    for (int i=0; i<num_words; i++)
        if (bitset[i] != 0)
            return i*BITS_PER_WORD + __builtin_ctzll(bitset[i]);
    return -1;
}

bool have_non_empty_intersection(unsigned long long *bitset1,
                                     unsigned long long *bitset2,
                                     int num_words)
{
    for (int i=0; i<num_words; i++)
        if (bitset1[i] & bitset2[i])
            return true;
    return false;
}

int first_nonzero_in_intersection(unsigned long long *bitset1,
                                     unsigned long long *bitset2,
                                     int num_words)
{
    for (int i=0; i<num_words; i++) {
        unsigned long long word_intersection = bitset1[i] & bitset2[i];
        if (word_intersection)
            return i*BITS_PER_WORD + __builtin_ctzll(word_intersection);
    }
    return -1;
}

void bitset_intersect_with(unsigned long long *bitset,
                                     unsigned long long *adj,
                                     int num_words)
{
    for (int i=0; i<num_words; i++)
        bitset[i] &= adj[i];
}

void bitset_intersection_with_complement(unsigned long long *src1,
                                     unsigned long long *src2,
                                     unsigned long long *dst,
                                     int num_words)
{
    for (int i=0; i<num_words; i++)
        dst[i] = src1[i] & ~src2[i];
}

void copy_bitset(unsigned long long *src,
                        unsigned long long *dest,
                        int num_words)
{
    for (int i=0; i<num_words; i++)
        dest[i] = src[i];
}

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
    int *vv;

    bool *not_useful;

    int *clause_to_unique_remaining_vtx;
    int *unique_remaining_vtx_to_clause;

    // in unit_propagate_once, each vertex that does not appear in any clause
    // has -2 as its reason.  Every other vertex has a clause index as its reason,
    // or -1 if the vertex does not have a reason
    int *reason;
    
    // this contains -2 for each vertex that does not appear in any clause,
    // and -1 for each vertex that appears in at least one clause.  It is used
    // to initialise reason at the start of unit_propagate_once()
    int *reason_template;

    // used in unit_propagate_once
    bool *vertex_has_been_propagated;

    int *vv_count;
    int *remaining_vv_count;

    // Used in colouring_bound():
    // last_clause[v] is the index of the last clause in which v appears
    int *last_clause;

    int *col_class;     // used in simple_colouring_bound()

    unsigned long long *unit_clause_vv_bitset;

    unsigned long long *to_colour;

    unsigned long long *candidates;

    long *residual_wt;

    struct IntVec unit_clause_indices;

    struct IntStack S;

    struct IntStackWithoutDups I;

    struct IntStackWithoutDups iset;

    struct ListOfClauses cc;

    struct ClauseMembership cm;
};

void init_PreAlloc(struct PreAlloc *pre_alloc, int n)
{
    pre_alloc->vv = malloc(n * sizeof(*pre_alloc->vv));
    pre_alloc->not_useful = malloc(n * sizeof(*pre_alloc->not_useful));
    pre_alloc->clause_to_unique_remaining_vtx = malloc(n * sizeof(*pre_alloc->clause_to_unique_remaining_vtx));
    pre_alloc->unique_remaining_vtx_to_clause = malloc(n * sizeof(*pre_alloc->unique_remaining_vtx_to_clause));
    pre_alloc->reason = malloc(n * sizeof(*pre_alloc->reason));
    pre_alloc->reason_template = malloc(n * sizeof(*pre_alloc->reason_template));
    pre_alloc->vertex_has_been_propagated = malloc(n * sizeof(*pre_alloc->vertex_has_been_propagated));
    pre_alloc->vv_count = malloc(n * sizeof(*pre_alloc->vv_count));
    pre_alloc->remaining_vv_count = malloc(n * sizeof(*pre_alloc->remaining_vv_count));
    pre_alloc->last_clause = malloc(n * sizeof(*pre_alloc->last_clause));
    pre_alloc->col_class = malloc(n * sizeof(*pre_alloc->col_class));
    pre_alloc->unit_clause_vv_bitset = malloc((n+BITS_PER_WORD-1)/BITS_PER_WORD * sizeof *pre_alloc->unit_clause_vv_bitset);
    pre_alloc->to_colour = malloc((n+BITS_PER_WORD-1)/BITS_PER_WORD * sizeof *pre_alloc->to_colour);
    pre_alloc->candidates = malloc((n+BITS_PER_WORD-1)/BITS_PER_WORD * sizeof *pre_alloc->candidates);
    pre_alloc->residual_wt = malloc(n * sizeof *pre_alloc->residual_wt);
    init_IntVec(&pre_alloc->unit_clause_indices);
    init_IntStack(&pre_alloc->S, n);
    init_IntStackWithoutDups(&pre_alloc->I, n);
    init_IntStackWithoutDups(&pre_alloc->iset, n);
    init_ListOfClauses(&pre_alloc->cc, n);
    init_ClauseMembership(&pre_alloc->cm, n);
}

void destroy_PreAlloc(struct PreAlloc *pre_alloc)
{
    free(pre_alloc->vv);
    free(pre_alloc->not_useful);
    free(pre_alloc->clause_to_unique_remaining_vtx);
    free(pre_alloc->unique_remaining_vtx_to_clause);
    free(pre_alloc->reason);
    free(pre_alloc->reason_template);
    free(pre_alloc->vertex_has_been_propagated);
    free(pre_alloc->vv_count);
    free(pre_alloc->remaining_vv_count);
    free(pre_alloc->last_clause);
    free(pre_alloc->col_class);
    free(pre_alloc->unit_clause_vv_bitset);
    free(pre_alloc->to_colour);
    free(pre_alloc->candidates);
    free(pre_alloc->residual_wt);
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
    int i = 0;
    int v;
    while (reason[v = c->vv.vals[i]] != -1)
        ++i;
    assert(i < c->vv.size);
    return v;
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
            if (r != -1 && !I->on_stack[r]) {
                push(S, r);
                push_without_dups(I, r);
            }
        }
    }
}

void unit_propagate_once(struct PreAlloc *pre_alloc, struct Graph *g, struct ListOfClauses *cc,
        struct IntStackWithoutDups *I)
{
    memset(pre_alloc->unit_clause_vv_bitset, 0, g->numwords * sizeof(unsigned long long));

    clear_IntStack(&pre_alloc->S);
    memcpy(pre_alloc->remaining_vv_count, pre_alloc->vv_count, cc->size * sizeof(int));

    for (int i=0; i<pre_alloc->unit_clause_indices.size; i++) {
        int clause_idx = pre_alloc->unit_clause_indices.vals[i];
        if (cc->clause[clause_idx].remaining_wt) {
            push(&pre_alloc->S, clause_idx);
            int v = cc->clause[clause_idx].vv.vals[0];
            pre_alloc->clause_to_unique_remaining_vtx[clause_idx] = v;
        }
    }

    memset(pre_alloc->vertex_has_been_propagated, 0, g->n * sizeof(bool));
    memcpy(pre_alloc->reason, pre_alloc->reason_template, g->n * sizeof(int));

    while (pre_alloc->S.size) {
        int u_idx = pop(&pre_alloc->S);
//        struct Clause *u = &cc->clause[u_idx];
        assert (pre_alloc->remaining_vv_count[u_idx]/*u->remaining_vv_count*/ == 1);
        int v = pre_alloc->clause_to_unique_remaining_vtx[u_idx];
        if (!pre_alloc->vertex_has_been_propagated[v]) {
            for (int i=g->nonadjlists[v].size; i--; ) {
                int w = g->nonadjlists[v].vals[i];
                if (pre_alloc->reason[w] == -1) {
                    pre_alloc->reason[w] = u_idx;
                    for (int j=0; j<pre_alloc->cm.vtx_to_clauses[w].size; j++) {
                        int c_idx = pre_alloc->cm.vtx_to_clauses[w].vals[j];
                        pre_alloc->remaining_vv_count[c_idx]--;
                        switch(pre_alloc->remaining_vv_count[c_idx]) {
                        case 1:
                            {
                                int x = get_unique_remaining_vtx(&pre_alloc->cc.clause[c_idx], pre_alloc->reason);
                                if (have_non_empty_intersection(pre_alloc->unit_clause_vv_bitset, g->bit_complement_nd[x], g->numwords)) {
                                    int y = first_nonzero_in_intersection(pre_alloc->unit_clause_vv_bitset, g->bit_complement_nd[x], g->numwords);
                                    assert(y != -1);
                                    int d_idx = pre_alloc->unique_remaining_vtx_to_clause[y];
                                    pre_alloc->reason[y] = c_idx;
                                    create_inconsistent_set(pre_alloc, g, I, d_idx, cc, pre_alloc->reason);
                                    return;
                                }
                                push(&pre_alloc->S, c_idx);
                                pre_alloc->clause_to_unique_remaining_vtx[c_idx] = x;
                                pre_alloc->unique_remaining_vtx_to_clause[x] = c_idx;
                                set_bit(pre_alloc->unit_clause_vv_bitset, x);
                                break;
                            }
                        case 0:
                            create_inconsistent_set(pre_alloc, g, I, c_idx, cc, pre_alloc->reason);
                            return;
                        }
                    }
                }
            }
        }
        pre_alloc->vertex_has_been_propagated[v] = true;
    }
}

// Note: this swaps the vertex to the end of its list, so that it can be
// re-added to the lists if necessary
void remove_from_clause_membership(int v, int clause_idx, struct ClauseMembership *cm,
        struct PreAlloc *pre_alloc)
{
    struct IntVec *cm_v = &cm->vtx_to_clauses[v];
    int i = 0;
    while (cm_v->vals[i] != clause_idx)
        ++i;
    assert(i < cm_v->size);
    cm_v->vals[i] = cm_v->vals[cm_v->size-1];
    cm_v->vals[cm_v->size-1] = clause_idx;
    cm_v->size--;
    if (cm_v->size == 0) {
        pre_alloc->reason_template[v] = -2;
    }
}

void fake_length_one_clause(struct Clause *clause, int clause_idx, int vtx_pos,
        struct PreAlloc *pre_alloc) {
    int tmp = clause->vv.vals[vtx_pos];
    clause->vv.vals[vtx_pos] = clause->vv.vals[0];
    clause->vv.vals[0] = tmp;
    for (int i=1; i<clause->vv.size; i++) {
        int v = clause->vv.vals[i];
        remove_from_clause_membership(v, clause_idx, &pre_alloc->cm, pre_alloc);
    }
    clause->vv.size = 1;
    pre_alloc->vv_count[clause_idx] = 1;
}

void unfake_length_one_clause(struct Clause *clause, int clause_idx, int vtx_pos, int clause_len,
        struct PreAlloc *pre_alloc) {
    clause->vv.size = clause_len;
    pre_alloc->vv_count[clause_idx] = clause_len;
    for (int i=1; i<clause_len; i++) {
        int v = clause->vv.vals[i];
        pre_alloc->cm.vtx_to_clauses[v].vals[pre_alloc->cm.vtx_to_clauses[v].size++] = clause_idx;
        if (pre_alloc->cm.vtx_to_clauses[v].size == 1) {
            pre_alloc->reason_template[v] = -1;
        }
    }
    int tmp = clause->vv.vals[vtx_pos];
    clause->vv.vals[vtx_pos] = clause->vv.vals[0];
    clause->vv.vals[0] = tmp;
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
//    for (int z=clause_len; z--; ) {
        clear_stack_without_dups(&pre_alloc->I);
        fake_length_one_clause(clause, clause_idx, z, pre_alloc);
        unit_propagate_once(pre_alloc, g, cc, &pre_alloc->I);
        unfake_length_one_clause(clause, clause_idx, z, clause_len, pre_alloc);
        if (pre_alloc->I.size==0) {
            pre_alloc->not_useful[clause->vv.vals[z]] = true;
            return false;
        }
        for (int i=0; i<pre_alloc->I.size; i++)
            push_without_dups(&pre_alloc->iset, pre_alloc->I.vals[i]);
    }
    return true;
}

long process_inconsistent_set(
        struct IntStackWithoutDups *iset,
        struct ListOfClauses *cc,
        struct ClauseMembership *cm,
        struct PreAlloc *pre_alloc)
{
    assert(iset->size > 0);

    // find max index and min remaining weight
    int max_idx = iset->vals[0];
    long min_wt = cc->clause[max_idx].remaining_wt;
    for (int i=1; i<iset->size; i++) {
        int c_idx = iset->vals[i];
        long wt = cc->clause[c_idx].remaining_wt;
        if (wt < min_wt)
            min_wt = wt;
        if (c_idx > max_idx)
            max_idx = c_idx;
    }

    for (int i=0; i<iset->size; i++) {
        int c_idx = iset->vals[i];
        struct Clause *c = &cc->clause[c_idx];
        c->remaining_wt -= min_wt;
        if (c->remaining_wt == 0) {
            // Remove references to this clause from CM
            for (int j=0; j<c->vv.size; j++) {
                int v = c->vv.vals[j];
                remove_from_clause_membership(v, c_idx, cm, pre_alloc);
            }
        }
    }
    cc->clause[max_idx].weight -= min_wt;  // decrease weight of last clause in set
    return min_wt;
}

bool any_vtx_not_useful(struct PreAlloc *pre_alloc, struct Clause *clause)
{
    for (int i=0; i<clause->vv.size; i++) {
        int v = clause->vv.vals[i];
        if (pre_alloc->not_useful[v])
            return true;
    }
    return false;
}

long unit_propagate(struct PreAlloc *pre_alloc, struct Graph *g, struct ListOfClauses *cc,
        long target_reduction, struct Params *params)
{
    if (target_reduction <= 0)
        return 0;

    for (int v=0; v<g->n; v++)
        clear_IntVec(&pre_alloc->cm.vtx_to_clauses[v]);

    for (int i=0; i<cc->size; i++) {
        struct Clause *clause = &cc->clause[i];
        pre_alloc->vv_count[i] = clause->vv.size;
        for (int j=0; j<clause->vv.size; j++) {
            int v = clause->vv.vals[j];
            push_to_IntVec(&pre_alloc->cm.vtx_to_clauses[v], i);
        }
    }

    _Static_assert(-1==~0, "Unable to set an array of ints to -1 using memset");
    memset(pre_alloc->reason_template, -1, g->n * sizeof(int));
    for (int v=0; v<g->n; v++)
        pre_alloc->reason_template[v] -= (pre_alloc->cm.vtx_to_clauses[v].size == 0);

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

        improvement += process_inconsistent_set(&pre_alloc->I, cc, &pre_alloc->cm, pre_alloc);
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
        memset(pre_alloc->not_useful, 0, g->n * sizeof(bool));
        for (int i=0; i<cc->size; i++) {
            struct Clause *clause = &cc->clause[i];
            if (clause->vv.size==1 && clause->remaining_wt>0)
                pre_alloc->not_useful[clause->vv.vals[0]] = true;
        }
#ifdef VERY_VERBOSE
        printf("VERY_VERBOSE {\"isets2\": [");
        sep = "";
#endif
        for (int i=0; i<cc->size; i++) {
            struct Clause *clause = &cc->clause[i];
            if (clause->vv.size != 2)
                continue;

            if (any_vtx_not_useful(pre_alloc, clause))
                continue;

            for (;;) {
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
                improvement += process_inconsistent_set(&pre_alloc->iset, cc, &pre_alloc->cm, pre_alloc);

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

void try_to_enlarge_clause(struct Graph *g, struct Clause *clause, struct PreAlloc *pre_alloc, int numwords)
{
    copy_bitset(pre_alloc->to_colour, pre_alloc->candidates, numwords);
    for (int i=0; i<clause->vv.size-1; i++)
        bitset_intersect_with(pre_alloc->candidates, g->bit_complement_nd[clause->vv.vals[i]], numwords);

    int vv_len = 0;
    int w;
    while ((w=first_set_bit(pre_alloc->candidates, numwords))!=-1) {
        unset_bit(pre_alloc->candidates, w);
        pre_alloc->vv[vv_len++] = w;
    }

// TODO: check if it works as well to just do:
//    for (int i=0; i<vv_len; i++) for (int j=i+1; j<vv_len; j++)
    for (int sum=0; sum<=vv_len*2-3; sum++) {
        int i_start = sum - vv_len + 1;
        if (i_start < 0)
            i_start = 0;
        for (int i=i_start, j=sum-i_start; i<j; i++, j--) {
            int w = pre_alloc->vv[i];
            int u = pre_alloc->vv[j];
            if (!g->adjmat[w][u]) {
                set_bit(pre_alloc->to_colour, clause->vv.vals[clause->vv.size-1]);
                clause->vv.size--;
                unset_bit(pre_alloc->to_colour, w);
                unset_bit(pre_alloc->to_colour, u);
                push_to_IntVec(&clause->vv, w);
                push_to_IntVec(&clause->vv, u);
                return;
            }
        }
    }
}

long do_colouring_without_reordering(struct PreAlloc *pre_alloc, struct Graph *g, int numwords)
{
    long bound = 0;
    int v;
    while ((v=first_set_bit(pre_alloc->to_colour, numwords))!=-1) {
        copy_bitset(pre_alloc->to_colour, pre_alloc->candidates, numwords);
        unset_bit(pre_alloc->to_colour, v);
        struct Clause *clause = &pre_alloc->cc.clause[pre_alloc->cc.size];
        clause->vv.size = 0;
        push_to_IntVec(&clause->vv, v);
        bitset_intersect_with(pre_alloc->candidates, g->bit_complement_nd[v], numwords);
        while ((v=first_set_bit(pre_alloc->candidates, numwords))!=-1) {
            unset_bit(pre_alloc->to_colour, v);
            push_to_IntVec(&clause->vv, v);
            bitset_intersect_with(pre_alloc->candidates, g->bit_complement_nd[v], numwords);
        }
        if (clause->vv.size > 1) {
            try_to_enlarge_clause(g, clause, pre_alloc, numwords);
        }

        long class_min_wt = pre_alloc->residual_wt[clause->vv.vals[0]];
        for (int i=1; i<clause->vv.size; i++) {
            int w = clause->vv.vals[i];
            if (pre_alloc->residual_wt[w] < class_min_wt)
                class_min_wt = pre_alloc->residual_wt[w];
        }

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

int calc_numwords(unsigned long long *P_bitset, int graph_num_words)
{
    for (int i=graph_num_words; i--; ) {
        if (P_bitset[i] != 0)
            return i+1;
    }
    return 0;
}

bool colouring_bound(struct PreAlloc *pre_alloc, struct Graph *g, struct UnweightedVtxList *P,
        unsigned long long *P_bitset, long *cumulative_wt_bound, long target, struct Params *params)
{
    int numwords = calc_numwords(P_bitset, g->numwords);
    if (numwords == 0)
        return false;

    copy_bitset(P_bitset, pre_alloc->to_colour, numwords);

    memcpy(pre_alloc->residual_wt, g->weight, g->n * sizeof(*pre_alloc->residual_wt));

    clear_ListOfClauses(&pre_alloc->cc);

    long bound = do_colouring_without_reordering(pre_alloc, g, numwords);

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

bool simple_colouring_bound(struct PreAlloc *pre_alloc, struct Graph *g, struct UnweightedVtxList *P,
        unsigned long long *P_bitset, long *cumulative_wt_bound, long target, struct Params *params)
{
    int numwords = calc_numwords(P_bitset, g->numwords);
    if (numwords == 0)
        return false;

    copy_bitset(P_bitset, pre_alloc->to_colour, numwords);

    memcpy(pre_alloc->residual_wt, g->weight, g->n * sizeof(*pre_alloc->residual_wt));

    P->size = 0;
    long bound = 0;
    int v;
    while ((v=first_set_bit(pre_alloc->to_colour, numwords))!=-1) {
        copy_bitset(pre_alloc->to_colour, pre_alloc->candidates, numwords);
        long class_min_wt = pre_alloc->residual_wt[v];
        unset_bit(pre_alloc->to_colour, v);
        int col_class_size = 1;
        pre_alloc->col_class[0] = v;
        bitset_intersect_with(pre_alloc->candidates, g->bit_complement_nd[v], numwords);
        while ((v=first_set_bit(pre_alloc->candidates, numwords))!=-1) {
            if (pre_alloc->residual_wt[v] < class_min_wt)
                class_min_wt = pre_alloc->residual_wt[v];
            unset_bit(pre_alloc->to_colour, v);
            pre_alloc->col_class[col_class_size++] = v;
            bitset_intersect_with(pre_alloc->candidates, g->bit_complement_nd[v], numwords);
        }
        bound += class_min_wt;
        for (int i=0; i<col_class_size; i++) {
            int w = pre_alloc->col_class[i];
            pre_alloc->residual_wt[w] -= class_min_wt;
            if (pre_alloc->residual_wt[w] > 0) {
                set_bit(pre_alloc->to_colour, w);
            } else {
                cumulative_wt_bound[P->size] = bound;
                P->vv[P->size++] = w;
            }
        }
    }
    return bound > target;
}

void expand(struct PreAlloc *pre_alloc, struct Graph *g, struct VtxList *C, unsigned long long *P_bitset,
        struct VtxList *incumbent, long *expand_call_count, struct Params *params)
{
    (*expand_call_count)++;
    if (*expand_call_count % 100000 == 0)
        check_for_timeout();
    if (is_timeout_flag_set()) return;

    if (bitset_empty(P_bitset, g->numwords) && C->total_wt>incumbent->total_wt) {
        copy_VtxList(C, incumbent);
        if (!params->quiet)
            printf("New incumbent of weight %ld\n", incumbent->total_wt);
    }

    long *cumulative_wt_bound = malloc(g->n * sizeof *cumulative_wt_bound);
    struct UnweightedVtxList P;
    init_UnweightedVtxList(&P, g->n);

    if (params->max_sat_level ?
                colouring_bound(
                        pre_alloc, g, &P, P_bitset, cumulative_wt_bound, incumbent->total_wt - C->total_wt, params) :
                simple_colouring_bound(
                        pre_alloc, g, &P, P_bitset, cumulative_wt_bound, incumbent->total_wt - C->total_wt, params)) {

        unsigned long long *new_P_bitset = malloc(g->numwords * sizeof(unsigned long long));
        for (int i=P.size-1; i>=0 && C->total_wt+cumulative_wt_bound[i]>incumbent->total_wt; i--) {
            int v = P.vv[i];

            unset_bit(P_bitset, v);
            bitset_intersection_with_complement(P_bitset, g->bit_complement_nd[v], new_P_bitset, g->numwords);

            vtxlist_push_vtx(g, C, v);
            expand(pre_alloc, g, C, new_P_bitset, incumbent, expand_call_count, params);
            vtxlist_pop_vtx(g, C);
        }
        free(new_P_bitset);
    }

    destroy_UnweightedVtxList(&P);
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

    unsigned long long *P_bitset = calloc(g->numwords, sizeof(unsigned long long));
    for (int v=0; v<ordered_graph->n; v++) set_bit(P_bitset, v);
    struct VtxList C;
    init_VtxList(&C, ordered_graph->n);

    struct PreAlloc pre_alloc;
    init_PreAlloc(&pre_alloc, g->n);

    expand(&pre_alloc, ordered_graph, &C, P_bitset, incumbent, expand_call_count, &params);

    destroy_PreAlloc(&pre_alloc);

    destroy_VtxList(&C);
    free(P_bitset);

    // Use vertex indices from original graph
    for (int i=0; i<incumbent->size; i++)
        incumbent->vv[i] = vv[incumbent->vv[i]];

    free_graph(ordered_graph);
    free(vv);
}
