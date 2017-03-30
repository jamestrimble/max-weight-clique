#include "data.h"
#include <stdlib.h>

void init_stack(struct IntStack *s)
{
    s->size = 0;
}

void push(struct IntStack *s, int val)
{
    if (s->size == BIGNUM)
        exit(1);
    s->vals[s->size++] = val;
}

int pop(struct IntStack *s)
{
    if (s->size == 0)
        exit(1);
    return s->vals[--s->size];
}


void init_queue(struct IntQueue *q)
{
    q->start = 0;
    q->size = 0;
}

bool queue_empty(struct IntQueue *q)
{
    return (q->size == 0);
}

void enqueue(struct IntQueue *q, int val)
{
    if (q->start + q->size == BIGNUM)
        exit(1);
    q->vals[q->start + q->size++] = val;
}

int dequeue(struct IntQueue *q)
{
    if (q->size == 0)
        exit(1);
    q->size--;
    return q->vals[q->start++];
}

void ClauseMembership_init(struct ClauseMembership *cm)
{
    for (int i=0; i<BIGNUM; i++)
        cm->list_len[i] = 0;
}
