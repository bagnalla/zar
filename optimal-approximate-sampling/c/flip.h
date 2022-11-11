// Flipping a coin.
// ** @author: fsaad@mit.edu

#ifndef FLIP_H
#define FLIP_H

extern unsigned long NUM_RNG_CALLS;

// Counter for tracking entropy usage.
int num_bits;

int flip(void);
int randint(int k);

#endif
