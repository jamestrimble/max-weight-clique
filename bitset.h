static void set_bit(unsigned long long bitset[WORDS_PER_BITSET], int bit) {
    bitset[bit/BITS_PER_WORD] |= (1ull << (bit%BITS_PER_WORD));
}

static void unset_bit(unsigned long long bitset[WORDS_PER_BITSET], int bit) {
    bitset[bit/BITS_PER_WORD] &= ~(1ull << (bit%BITS_PER_WORD));
}

static int last_set_bit(unsigned long long bitset[WORDS_PER_BITSET], int num_words) {
    for (int i=num_words-1; i>=0; i--) {
        if (bitset[i] != 0)
            return i*BITS_PER_WORD + (BITS_PER_WORD-1-__builtin_clzll(bitset[i]));
    }
    return -1;
}

static void reject_adjacent_vertices(unsigned long long bitset[WORDS_PER_BITSET], unsigned long long adj[WORDS_PER_BITSET],
        int num_words) {
    for (int i=0; i<num_words; i++) {
        bitset[i] &= ~adj[i];
    }
}

static void copy_bitset(unsigned long long src[WORDS_PER_BITSET], unsigned long long dest[WORDS_PER_BITSET],
        int num_words) {
    for (int i=0; i<num_words; i++)
        dest[i] = src[i];
}

