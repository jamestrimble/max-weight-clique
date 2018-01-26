#include <stdbool.h>

#define BIGNUM 2000

struct IntStack {
    int size;
    int vals[BIGNUM];
};

void init_stack(struct IntStack *s);

void push(struct IntStack *s, int val);

int pop(struct IntStack *s);


struct IntStackWithoutDups {
    int size;
    int vals[BIGNUM];
    bool on_stack[BIGNUM];
};

void fast_init_stack_without_dups(struct IntStackWithoutDups *s,
        int max_member_val);

void init_stack_without_dups(struct IntStackWithoutDups *s);

void push_without_dups(struct IntStackWithoutDups *s, int val);

int pop_without_dups(struct IntStackWithoutDups *s);


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
    long remaining_wt;
};


struct ListOfClauses {
    struct Clause clause[BIGNUM];
    int size;
};

// Which clauses does each vertex belong to?
struct ClauseMembership {
    int list[BIGNUM][BIGNUM];
    int list_len[BIGNUM];
};

void ClauseMembership_init(struct ClauseMembership *cm);

void fast_ClauseMembership_init(struct ClauseMembership *cm,
        int num_vertices);
