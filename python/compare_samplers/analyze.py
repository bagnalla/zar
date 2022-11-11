from collections import namedtuple
from itertools import count, takewhile
import math
from math import factorial, sqrt
import csv
import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import cumfreq, describe, relfreq

Record = namedtuple('Record', 'sample bits')

N = 200

def pmf(k):
    return 1 / N if 0 <= k and k < N else 0

# d is the empirical dictionary, true_d an association list of support
# of the true distribution.
def total_variation(d, true_d):
    return sum(abs(lookup(i, d) - p) for i, p in true_d) / 2

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
    # Analyze sample values.
    samples = [int(r.sample) for r in records]
    samples_d = describe(samples)
    unique_samples = range(min(samples), max(samples) + 1)

    print("\n Samples:")
    print("μ: %f" % samples_d.mean)
    print("σ: %f" % sqrt(samples_d.variance))

    true_d = list(takewhile(lambda x: x[1] > 0, ((i, pmf(i)) for i in count(0))))

    samples_hist = relfreq(samples, numbins=len(unique_samples))
    d = list(zip(count(1), samples_hist.frequency))
    dd = dict(d)
    print("total variation distance: %f" % total_variation(dd, true_d))
    print("KL divergence: %f" % KL(dd, true_d))
    print("SMAPE: %f" % smape(d))

    # Analyze sample bitstring lengths.
    bitstring_lengths = [r.bits for r in records]
    bitstring_lengths_d = describe(bitstring_lengths)

    print("\nBits:")
    print("μ: %f" % bitstring_lengths_d.mean)
    print("σ: %f" % sqrt(bitstring_lengths_d.variance))
    print("Σ: %f" % sum(bitstring_lengths))

print("N = %d" % N)

print('\nFLDR (C)')
with open('fldr_c_samples.dat', newline='') as csvfile:
     reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
     records = [Record(row[0], int(row[1])) for row in reader]
     analyze(records)

print('\nFLDR (Python)')
with open('fldr_python_samples.dat', newline='') as csvfile:
     reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
     records = [Record(row[0], int(row[1])) for row in reader]
     analyze(records)

print('\nOPTAS (C)')
with open('optas_c_samples.dat', newline='') as csvfile:
     reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
     records = [Record(row[0], int(row[1])) for row in reader]
     analyze(records)

print('\nOPTAS (Python)')
with open('optas_python_samples.dat', newline='') as csvfile:
     reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
     records = [Record(row[0], int(row[1])) for row in reader]
     analyze(records)

print('\nZar (Python)')
with open('zar_python_samples.dat', newline='') as csvfile:
     reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
     records = [Record(row[0], int(row[1])) for row in reader]
     analyze(records)
