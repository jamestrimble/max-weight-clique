#include <stdbool.h>

#define BIGNUM 500

struct IntStack {
    int size;
    int vals[BIGNUM];
};

void init_stack(struct IntStack *s);

void push(struct IntStack *s, int val);

int pop(struct IntStack *s);


struct IntQueue {
    int start;
    int size;
    int vals[BIGNUM];
};

void init_queue(struct IntQueue *q);

bool queue_empty(struct IntQueue *q);

void enqueue(struct IntQueue *q, int val);

int dequeue(struct IntQueue *q);


struct Clause {
    long weight;
    int vv[BIGNUM];
    int vv_len;
    int remaining_vv_count;
    bool used;    // has it been used in an inconsistent subset?
    bool was_pushed_to_Q;
};


struct ListOfClauses {
    struct Clause cc[BIGNUM];
    int size;
};

struct ClauseMembership {
    int list[BIGNUM][BIGNUM];
    int list_len[BIGNUM];
};

void ClauseMembership_init(struct ClauseMembership *cm);
