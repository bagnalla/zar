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

p = 2/3

# d is the empirical dictionary, true_d an association list of support
# of the true distribution.
def total_variation(d, true_d):
    return sum(abs(lookup(i, d) - q) for i, q in true_d) / 2

def log2(n):
    return 0 if n == 0 else math.log2(n)

def KL(d, true_d):
    return sum(lookup(i, d) * log2(lookup(i, d) / q) for i, q in true_d)

# # Symmetric mean absolute percentage error. From ProbFuzz paper pg 7.
# def smape(d):
#     return sum(abs(q - p) / (abs(q) + p) for i, q in d) \
#         / len(d)

# Dictionary lookup with default 0.
def lookup(key, d):
    return d.get(key) or 0

def analyze(records):
    print("# samples: %d" % len(records))

    # Analyze sample values.
    samples = [int(r.sample) for r in records]
    samples_d = describe(samples)
    unique_samples = range(min(samples), max(samples) + 1)

    print("\nSamples:")
    print("μ: %f" % samples_d.mean)
    print("σ: %f" % sqrt(samples_d.variance))

    true_d = [(0, 1 - p), (1, p)]

    samples_hist = relfreq(samples, numbins=len(unique_samples))
    d = list(zip(count(), samples_hist.frequency))
    dd = dict(d)
    print("total variation distance: %f" % total_variation(dd, true_d))
    print("KL divergence: %f" % KL(dd, true_d))
    # print("SMAPE: %f" % smape(d))

    # Analyze sample bitstring lengths.
    bitstring_lengths = [len(r.bits) for r in records]
    bitstring_lengths_d = describe(bitstring_lengths)
    
    unique_bitstring_lengths = [*set(bitstring_lengths)]
    unique_bitstring_lengths.sort()

    bitstring_lengths_hist = relfreq(bitstring_lengths,
                                     numbins=len(unique_bitstring_lengths))
    freqs = bitstring_lengths_hist.frequency

    print("\nBits:")
    print("μ: %f" % bitstring_lengths_d.mean)
    print("σ: %f" % sqrt(bitstring_lengths_d.variance))

    # Analyze sample times
    times = [r.time for r in records]
    times_d = describe(times)

    print("\nTime:")
    print("μₜ: %f" % times_d.mean)
    print("σₜ: %f" % sqrt(times_d.variance))
    print("Σₜ: %f" % sum(times))

with open('samples100k.dat', newline='') as csvfile:
     reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
     records = [Record(row[0], row[1], float(row[2])) for row in reader]
     analyze(records)
