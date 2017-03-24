#define _GNU_SOURCE

#include "graph.h"

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

static void fail(char* msg) {
    printf("%s\n", msg);
    exit(1);
}

void add_edge(struct Graph *g, int v, int w) {
    g->adjmat[v][w] = true;
    g->adjmat[w][v] = true;
}

// Precondition: *g is already zeroed out
void readGraph(char* filename, struct Graph* g) {
    FILE* f;
    
    if ((f=fopen(filename, "r"))==NULL)
        fail("Cannot open file");

    char* line = NULL;
    size_t nchar = 0;

    int nvertices = 0;
    int medges = 0;
    int v, w;
    int edges_read = 0;
    long wt;

    ssize_t retval;
    while ((retval=getline(&line, &nchar, f)) != -1) {
        if (nchar > 0) {
            switch (line[0]) {
            case 'p':
                if (sscanf(line, "p edge %d %d", &nvertices, &medges)!=2)
                    fail("Error reading a line beginning with p.\n");
                printf("%d vertices\n", nvertices);
                if (nvertices >= MAX_N)
                    fail("Too many vertices. Please recompile with a larger MAX_N.\n");
                printf("%d edges\n", medges);
                g->n = nvertices;
                g->bitset_words = (g->n + (BITS_PER_WORD-1)) / BITS_PER_WORD;
                for (int i=0; i<nvertices; i++)
                    g->weight[i] = 1l;   // default weight
                break;
            case 'e':
                if (sscanf(line, "e %d %d", &v, &w)!=2)
                    fail("Error reading a line beginning with e.\n");
                add_edge(g, v-1, w-1);
                edges_read++;
                break;
            case 'n':
                if (sscanf(line, "n %d %ld", &v, &wt)!=2)
                    fail("Error reading a line beginning with n.\n");
                g->weight[v-1] = wt;
                break;
            }
        }
    }

    if (medges>0 && edges_read != medges) fail("Unexpected number of edges.");

    fclose(f);
}
