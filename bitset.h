#ifndef BITSET_H
#define BITSET_H

void set_bit(unsigned long long *bitset, int bit);

void unset_bit(unsigned long long *bitset, int bit);

int last_set_bit(unsigned long long *bitset, int num_words);

int first_set_bit(unsigned long long *bitset, int num_words);

void bitset_intersect_with(unsigned long long *bitset,
                                     unsigned long long *adj,
                                     int num_words);

void copy_bitset(unsigned long long *src,
                        unsigned long long *dest,
                        int num_words);

#endif
