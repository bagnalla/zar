from collections import namedtuple
from itertools import count, takewhile
import math
from math import factorial, sqrt
import csv
import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import cumfreq, describe, relfreq

Record = namedtuple('Record', 'sample bits time')

N = 200

# def comb(n, k):
#     return factorial(n) / (factorial(k) * factorial(n - k))

def pmf(k):
    return 1 / N if 0 <= k and k < N else 0

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
    return sum(abs(p - pmf(i)) / (abs(p) + abs(pmf(i))) for i, p in d) \
        / len(d)

# Dictionary lookup with default 0.
def lookup(key, d):
    return d.get(key) or 0

def analyze(records):
    print("N = %d" % N)
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

    # print("pmf:")
    # # print(sum(cond_pmf(i, 0.5, 1, 3) for i in range(3, 100)))
    # print([(i, cond_pmf(i, 0.5, 1, 3)) for i in range(3, 10)])

    true_d = list(takewhile(lambda x: x[1] > 0, ((i, pmf(i)) for i in count(1))))

    samples_hist = relfreq(samples, numbins=len(unique_samples))
    d = list(zip(count(1), samples_hist.frequency))
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
    print("Σ: %f" % sum(bitstring_lengths))

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

with open('samples100k.dat', newline='') as csvfile:
     reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
     records = [Record(row[0], row[1], float(row[2])) for row in reader]
     analyze(records)
