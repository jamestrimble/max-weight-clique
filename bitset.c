#ifndef BITSET_H
#define BITSET_H

#include "graph.h" 

bool test_bit(unsigned long long *bitset, int bit)
{
    return 0 != (bitset[bit/BITS_PER_WORD] & (1ull << (bit%BITS_PER_WORD)));
}

void set_bit(unsigned long long *bitset, int bit)
{
    bitset[bit/BITS_PER_WORD] |= (1ull << (bit%BITS_PER_WORD));
}

void unset_bit(unsigned long long *bitset, int bit)
{
    bitset[bit/BITS_PER_WORD] &= ~(1ull << (bit%BITS_PER_WORD));
}

int bitset_popcount(unsigned long long *bitset, int num_words)
{
    int count = 0;
    for (int i=0; i<num_words; i++)
        count += __builtin_popcountll(bitset[i]);
    return count;
}

bool bitset_empty(unsigned long long *bitset, int num_words)
{
    for (int i=0; i<num_words; i++)
        if (bitset[i] != 0)
            return false;
    return true;
}

int last_set_bit(unsigned long long *bitset, int num_words)
{
    for (int i=num_words-1; i>=0; i--)
        if (bitset[i] != 0)
            return i*BITS_PER_WORD + (BITS_PER_WORD-1-__builtin_clzll(bitset[i]));
    return -1;
}

int first_set_bit(unsigned long long *bitset,
                         int num_words)
{
    for (int i=0; i<num_words; i++)
        if (bitset[i] != 0)
            return i*BITS_PER_WORD + __builtin_ctzll(bitset[i]);
    return -1;
}

void bitset_intersect_with(unsigned long long *bitset,
                                     unsigned long long *adj,
                                     int num_words)
{
    for (int i=0; i<num_words; i++)
        bitset[i] &= adj[i];
}

void copy_bitset(unsigned long long *src,
                        unsigned long long *dest,
                        int num_words)
{
    for (int i=0; i<num_words; i++)
        dest[i] = src[i];
}

#endif
