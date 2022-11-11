# Released under Apache 2.0; refer to LICENSE.txt

# Slightly modified by Alex Bagnall to track entropy usage (original
# code taken from https://github.com/probcomp/fast-loaded-dice-roller
# on Oct 25, 2022.

from collections import namedtuple
from random import getrandbits

fldr_s = namedtuple('fldr_s', ['n', 'm', 'k', 'r', 'h', 'H'])

def flip():
    return getrandbits(1)

def fldr_preprocess_int(a):
    n = len(a)
    m = sum(a)
    k = (m-1).bit_length() # ceil(log2(m))
    r = (1 << k) - m

    h = [0] * k
    H = [[-1]*k for _i in range(n+1)]
    for j in range(k):
        d = 0
        for i in range(n):
            w = (a[i] >> ((k-1) - j)) & 1
            h[j] += (w > 0)
            if w > 0:
                H[d][j] = i
                d += 1
        w = (r >> ((k-1) - j)) & 1
        h[j] += (w > 0)
        if w > 0:
            H[d][j] = n

    return fldr_s(n, m, k, r, h, H)

def fldr_sample(x):
    # Counter to track entropy usage.
    num_bits = 0

    n, h, H = x.n, x.h, x.H
    if n == 1:
        return 0, num_bits
    d = 0
    c = 0
    while True:
        num_bits += 1
        b = flip()
        d = 2*d + (1 - b)
        if d < h[c]:
            z = H[d][c]
            if z < n:
                return z, num_bits
            else:
                d = 0
                c = 0
        else:
            d = d - h[c]
            c = c + 1
