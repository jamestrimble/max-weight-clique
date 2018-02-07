#include "graph.h"

struct Params
{
    int max_sat_level;
    int vtx_ordering;
    bool quiet;
};

void mc(struct Graph* g, long *expand_call_count,
        struct Params params, struct VtxList *incumbent);

