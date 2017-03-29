#define vertex_order_help \
        "Set vertex ordering heuristic (0=no sorting, 1=increasing deg, " \
        "-1=decreasing deg, 2=increasing weight, -2=decreasing weight, " \
        "3=increasing weighted degree, -3=decreasing weighted degree, " \
        "4=increasing weighted degree plus weight, -4=decreasing weighted degree plus weight, " \
        "9=increasing deg/wt, -9=decreasing deg/wt"

void order_vertices(int *vv, struct Graph *g, int vtx_ordering);

