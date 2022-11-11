from collections import namedtuple
from itertools import takewhile
import math
from math import exp, factorial, sqrt
from itertools import count, islice
import csv
import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import cumfreq, describe, relfreq

Record = namedtuple('Record', 'sample bits')

def comb(n, k):
    return factorial(n) / (factorial(k) * factorial(n - k))

def integers():
    yield 0
    for i in count(1):
        yield i
        yield -i

def shift(x, gen):
    for y in gen:
        yield x + y

mu = 10
sigma = 2

def num(x):
    return exp(- (x - mu)**2 / (2 * sigma**2))

# def denom():
#     return num(mu) + sum(takewhile(lambda x: x > 0,
#                                    (num(i) for i in shift(mu, integers()))))

denom = sum(takewhile(lambda x: x > 0, (num(i) for i in shift(mu, integers()))))

def pmf(k):
    return num(k) / denom

print(pmf(0))

# # Condition on n <= k.
# def cond_pmf(k, p, r, n):
#     return pmf(k, p, r) / (1 - sum([pmf(i, p, r) for i in range(n)]))

# def true_pmf(k):
#     return cond_pmf(k, 1/5, 1, 3)

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
    # print(true_d)
    return sum(lookup(i, d) * log2(lookup(i, d) / p) for i, p in true_d)

# Symmetric mean absolute percentage error. From ProbFuzz paper pg 7.
def smape(d):
    return sum(abs(p - pmf(i)) / (abs(p) + abs(pmf(i))) for i, p in d) \
        / len(d)

# # Approximate Shannon entropy.
# def entropy():
#     return -sum([pmf(i) * log2(pmf(i)) for i in range(3, 1000)])

# Dictionary lookup with default 0.
def lookup(key, d):
    return d.get(key) or 0

def analyze(records):
    print("# samples: %d" % len(records))

    # Analyze sample values.
    samples = [int(r.sample) for r in records]
    samples_d = describe(samples)
    unique_samples = range(min(samples), max(samples) + 1)
    # unique_samples = [*set(samples)]
    # unique_samples.sort()
    # print(samples)

    print("\nSamples:")
    print("μ: %f" % samples_d.mean)
    print("σ: %f" % sqrt(samples_d.variance))
    # print("Σ: %f" % sum(samples))

    # print("pmf:")
    # # print(sum(cond_pmf(i, 0.5, 1, 3) for i in range(3, 100)))
    # print([(i, cond_pmf(i, 0.5, 1, 3)) for i in range(3, 10)])

    # print([0] + list(islice(integers(), 1000)))
    # true_d = [(0, pmf(0))] + [(i, pmf(i)) for i in islice(integers(), 1000)]
    true_d = list(takewhile(lambda x: x[1] > 0, ((i, pmf(i)) for i in integers())))
    # print(true_d)

    samples_hist = relfreq(samples, numbins=len(unique_samples))
    # print(samples_hist)
    d = list(zip(count(math.ceil(samples_hist.lowerlimit)), samples_hist.frequency))
    dd = dict(d)

    # print("total variation distance: %f" % total_variation(dd, true_d))
    # print("KL divergence: %f" % KL(dd, true_d))
    # print("SMAPE: %f" % smape(d))

    # print(list(d))
    # print(dict(list(d)))
    # print(lookup(3, dict(list(d))))

    # # Analyze sample bitstring lengths.
    bitstring_lengths = [r.bits for r in records]
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

    # e = entropy()
    # print("\nshannon entropy: %f" % e)
    # print("δ: %f" % (bitstring_lengths_d.mean - e))

with open('samples100k.dat', newline='') as csvfile:
     reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
     records = [Record(row[0], int(row[1])) for row in reader]
     analyze(records)
