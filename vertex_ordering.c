#include <stdio.h>
#include <stdlib.h>

#include "graph.h"
#include "sorting.h"
#include "util.h"

double inc_deg_key(struct Graph *g, int v) { return g->degree[v]; }
double dec_deg_key(struct Graph *g, int v) { return -g->degree[v]; }
double inc_weighted_deg_key(struct Graph *g, int v) { return g->weighted_deg[v]; }
double dec_weighted_deg_key(struct Graph *g, int v) { return -g->weighted_deg[v]; }
double inc_weighted_deg_plus_wt_key(struct Graph *g, int v) { return g->weighted_deg[v] + g->weight[v]; }
double dec_weighted_deg_plus_wt_key(struct Graph *g, int v) { return -g->weighted_deg[v] - g->weight[v]; }
double inc_wt_key(struct Graph *g, int v) { return g->weight[v]; }
double dec_wt_key(struct Graph *g, int v) { return -g->weight[v]; }

double inc_wt_over_deg_key(struct Graph *g, int v) {
    return (double)g->weight[v] / g->degree[v];
}
double dec_wt_over_deg_key(struct Graph *g, int v) {
    return -(double)g->weight[v] / g->degree[v];
}

void calc_weighted_degs(struct Graph *g) {
    for (int i=0; i<g->n; i++) {
        g->weighted_deg[i] = 0;
        for (int j=0; j<g->n; j++) {
            if (g->adjmat[i][j]) {
                g->weighted_deg[i] += g->weight[j];
            }
        }
    }
}

void carraghan_pardalos_order(int *vv, struct Graph *g, bool reverse) {
    long *residual_weighted_deg = malloc(g->n * sizeof(*residual_weighted_deg));
    for (int i=0; i<g->n; i++)
        residual_weighted_deg[i] = g->weighted_deg[i];

    for (int i=0; i<g->n; i++) {
        // find vertex with lowest residual_weighted_deg
        int best_v_pos = -1;
        long best_wt_deg = LONG_MAX;
        for (int j=i; j<g->n; j++) {
            int v = vv[j];
            if (residual_weighted_deg[v] < best_wt_deg) {
                best_wt_deg = residual_weighted_deg[v];
                best_v_pos = j;
            }
        }
        int v = vv[best_v_pos];
        vv[best_v_pos] = vv[i];
        vv[i] = v;

        for (int j=i+1; j<g->n; j++) {
            int w = vv[j];
            if (g->adjmat[v][w])
                residual_weighted_deg[w] -= g->weight[v];
        }
    }

    if (reverse) {
        for (int i=0; i<g->n/2; i++) {
            int tmp = vv[i];
            vv[i] = vv[g->n - 1 - i];
            vv[g->n - 1 - i] = tmp;

        }
    }
    free(residual_weighted_deg);
}
void order_vertices(int *vv, struct Graph *g, int vtx_ordering) {
    for (int i=0; i<g->n; i++)
        vv[i] = i;

    switch(vtx_ordering) {
    case  0: break;  // no sorting
    case  1: INSERTION_SORT_VV(inc_deg_key) break;
    case -1: INSERTION_SORT_VV(dec_deg_key) break;
    case  2: INSERTION_SORT_VV(inc_wt_key) break;
    case -2: INSERTION_SORT_VV(dec_wt_key) break;
    case  3: calc_weighted_degs(g); INSERTION_SORT_VV(inc_weighted_deg_key) break;
    case -3: calc_weighted_degs(g); INSERTION_SORT_VV(dec_weighted_deg_key) break;
    case  4: calc_weighted_degs(g); INSERTION_SORT_VV(inc_weighted_deg_plus_wt_key) break;
    case -4: calc_weighted_degs(g); INSERTION_SORT_VV(dec_weighted_deg_plus_wt_key) break;
    case  5: calc_weighted_degs(g); carraghan_pardalos_order(vv, g, false); break;
    case -5: calc_weighted_degs(g); carraghan_pardalos_order(vv, g, true); break;
    case  9: INSERTION_SORT_VV(inc_wt_over_deg_key) break;
    case -9: INSERTION_SORT_VV(dec_wt_over_deg_key) break;
    case 10: INSERTION_SORT_VV(dec_deg_key) break;
    default: fail("Unrecognised vertex order");
    }
}


