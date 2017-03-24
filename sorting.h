#define INSERTION_SORT(type, arr, arr_len, swap_condition) do { \
    for (int i=1; i<arr_len; i++) {                             \
        for (int j=i; j>=1; j--) {                              \
            if (swap_condition) {                               \
                type tmp = arr[j-1];                            \
                arr[j-1] = arr[j];                              \
                arr[j] = tmp;                                   \
            } else {                                            \
                break;                                          \
            }                                                   \
        }                                                       \
    }                                                           \
} while(0);

#define INSERTION_SORT_VV(key_function)                                        \
    INSERTION_SORT(int, vv, g->n,                                              \
        (key_function(g, vv[j-1]) > key_function(g, vv[j]) ||                  \
        (key_function(g, vv[j-1])==key_function(g, vv[j]) && vv[j-1]>vv[j])))


