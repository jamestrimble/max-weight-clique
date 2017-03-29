#include <stdio.h>
#include <stdlib.h>

void fail(char* msg) {
    fprintf(stderr, "%s\n", msg);
    exit(1);
}


