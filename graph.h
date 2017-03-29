#ifndef GRAPH_H
#define GRAPH_H

#define MAX_N 4001

#include <limits.h>
#include <stdbool.h>

#define BYTES_PER_WORD sizeof(unsigned long long)
#define BITS_PER_WORD (CHAR_BIT * BYTES_PER_WORD)
#define WORDS_PER_BITSET ((MAX_N+(BITS_PER_WORD-1))/BITS_PER_WORD)

//struct Graph {
//    int n;
//    int *degree;                    // the degree of each vertex
//    edge_label_t **adjmat;          // each element points to a row of the adjacency matrix
//    unsigned int *label;            // a label for each vertex
//    edge_label_t *adjmat_elements;  // a flat array containing the n*n elements of the adj. matrix
//};

struct Graph {
    int n;
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

void populate_bitadjmat(struct Graph *g);

struct Graph *induced_subgraph(struct Graph *g, int *vv, int vv_len);

struct Graph *new_graph(int n);

void free_graph(struct Graph *g);

// Precondition: *g is already zeroed out
void readGraph(char* filename, struct Graph* g);

#endif
