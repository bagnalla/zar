from collections import namedtuple
from itertools import takewhile
import math
from math import factorial, sqrt
from itertools import count
import csv
import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import cumfreq, describe, relfreq

Record = namedtuple('Record', 'sample bits time')

def comb(n, k):
    return factorial(n) / (factorial(k) * factorial(n - k))

# Negative binomial distribution wrt probability p. Geometric when
# r=1. Pr(X) = k
def pmf(k, p, r):
    # return comb(k + r - 1, r - 1) * (1 - p)**k * p**r
    return comb(k + r - 1, r - 1) * p**k * (1 - p)**r

# print(pmf(0, 1/2, 1))

def is_prime(n):
    if n == 1:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(sqrt(n)) + 1):
        if n % i == 0:
            return False
    return True

def primes():
    yield 2
    for n in range(3, 1000, 2):
        if is_prime(n):
            yield n

def nonprimes():
    for n in range(1000):
        if not is_prime(n):
            yield n

# print(list(nonprimes()))

p = 2/3
r = 1
norm = sum([pmf(i, p, r) for i in primes()])

# Condition on n <= k.
def cond_pmf(k):
    # return pmf(k, p, r) / (1 - sum([pmf(i, p, r) for i in range(n)]))
    return (pmf(k, p, r) / norm) if is_prime(k) else 0

print(cond_pmf(2))

def true_pmf(k):
    return cond_pmf(k)

# print([(i, true_pmf(i)) for i in range(1000)])
# print(sum([true_pmf(i) for i in range(1000)]))

# Calculate total variation difference between the empirical and true
# distributions.
# def total_variation(d):
#     return max(abs(p - true_pmf(i)) for (i, p) in d)

# d is the empirical dictionary, true_d an association list of support
# of the true distribution.
def total_variation(d, true_d):
    return sum(abs(lookup(i, d) - p) for i, p in true_d) / 2

# Calculate KL divergence (relative entropy) from the true
# distribution to the empirical distribution.
# def KL(d):
#     return sum(p * log2(p / true_pmf(i)) for (i, p) in d)

def log2(n):
    return 0 if n == 0 else math.log2(n)

def KL(d, true_d):
    return sum(lookup(i, d) * log2(lookup(i, d) / p) for i, p in true_d)

# Symmetric mean absolute percentage error. From ProbFuzz paper pg 7.
def smape(d):
    return sum(abs(p - true_pmf(i)) / (abs(p) + abs(true_pmf(i))) for i, p in d) \
        / len(d)

# Approximate Shannon entropy.
def entropy():
    return -sum([true_pmf(i) * log2(true_pmf(i)) for i in range(3, 1000)])

def rel_freqs(samples, unique_samples):
    return [len(list(filter(lambda x: x == k, samples))) / len(samples) for k in unique_samples]

# Dictionary lookup with default 0.
def lookup(key, d):
    return d.get(key) or 0

def analyze(records):
    print("# samples: %d" % len(records))

    # Analyze sample values.
    samples = [int(r.sample) for r in records]
    samples_d = describe(samples)
    max_sample = max(samples)
    unique_samples = list(filter(lambda n: n <= max_sample, primes()))
    # unique_samples = [*set(samples)]
    # unique_samples.sort()
    # print(samples)
    # print(len(list(filter(lambda x: x == 2, samples))))
    # print(unique_samples)

    print("\nSamples:")
    print("μ: %f" % samples_d.mean)
    print("σ: %f" % sqrt(samples_d.variance))
    # print("Σ: %f" % sum(samples))

    # print("pmf:")
    # # print(sum(cond_pmf(i, 0.5, 1, 3) for i in range(3, 100)))
    # print([(i, cond_pmf(i, 0.5, 1, 3)) for i in range(3, 10)])

    # true_d = [(i, true_pmf(i)) for i in range(1000)]
    true_d = [(i, true_pmf(i)) for i in primes()][:60]
    # print(true_d[:10])

    # samples_hist = relfreq(samples, numbins=len(unique_samples))
    samples_freqs = rel_freqs(samples, unique_samples)
    d = list(zip(primes(), samples_freqs))
    # print(d)
    dd = dict(d)
    print("total variation distance: %f" % total_variation(dd, true_d))
    print("KL divergence: %f" % KL(dd, true_d))
    print("SMAPE: %f" % smape(d))

    # print(list(d))
    # print(dict(list(d)))
    # print(lookup(3, dict(list(d))))

    # # Analyze sample bitstring lengths.
    bitstring_lengths = [len(r.bits) for r in records]
    bitstring_lengths_d = describe(bitstring_lengths)
    
    unique_bitstring_lengths = [*set(bitstring_lengths)]
    unique_bitstring_lengths.sort()
    # print(unique_bitstring_lengths)

    bitstring_lengths_hist = relfreq(bitstring_lengths,
                                     numbins=len(unique_bitstring_lengths))
    freqs = bitstring_lengths_hist.frequency
    # print(bitstring_lengths_hist)
    # print(freqs)

    print("\nBits:")
    print("μ: %f" % bitstring_lengths_d.mean)
    print("σ: %f" % sqrt(bitstring_lengths_d.variance))
    # print("Σ: %f" % sum(bitstring_lengths))

    # samples_hist = relfreq(samples, numbins=len(unique_samples))
    # # freqs = samples_hist.frequency
    # freqs = list(takewhile(lambda x: x >= 0.01, samples_hist.frequency))
    # unique_samples = unique_samples[:len(freqs)]

    # # Check that the relative freqencies sum to 1.
    # # print(np.sum(bitstring_lengths_hist.frequency))

    # Analyze sample times
    times = [r.time for r in records]
    times_d = describe(times)
    # print(times_d)

    print("\nTime:")
    print("μₜ: %f" % times_d.mean)
    print("σₜ: %f" % sqrt(times_d.variance))
    print("Σₜ: %f" % sum(times))

    e = entropy()
    print("\nshannon entropy: %f" % e)
    print("δ: %f" % (bitstring_lengths_d.mean - e))

with open('samples100k.dat', newline='') as csvfile:
     reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
     records = [Record(row[0], row[1], float(row[2])) for row in reader]
     analyze(records)
