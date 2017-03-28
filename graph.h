#define MAX_N 4001

#include <limits.h>
#include <stdbool.h>

#define BYTES_PER_WORD sizeof(unsigned long long)
#define BITS_PER_WORD (CHAR_BIT * BYTES_PER_WORD)
#define WORDS_PER_BITSET ((MAX_N+(BITS_PER_WORD-1))/BITS_PER_WORD)

struct Graph {
    int n;
    int bitset_words;
    int degree[MAX_N];
    long weighted_deg[MAX_N];
    long weight[MAX_N];
    bool adjmat[MAX_N][MAX_N];
    unsigned long long bitadjmat[MAX_N][WORDS_PER_BITSET];
};

struct VtxList {
    long total_wt;
    int size;
    int vv[MAX_N];
};

struct UnweightedVtxList {
    int size;
    int vv[MAX_N];
};

void add_edge(struct Graph *g, int v, int w);

void calculate_all_degrees(struct Graph *g);

// Checks if a set of vertices induces a clique
bool check_clique(struct Graph* g, struct VtxList* clq);

// Precondition: *g is already zeroed out
void readGraph(char* filename, struct Graph* g);
