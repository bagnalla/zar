from collections import namedtuple
from itertools import count, takewhile
import math
from math import factorial, sqrt
import csv
import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import cumfreq, describe, relfreq

Record = namedtuple('Record', 'sample bits time')

def analyze(records):
    print("# samples: %d" % len(records))

    # Analyze sample values.
    samples = [int(r.sample) for r in records]
    samples_d = describe(samples)
    unique_samples = range(min(samples), max(samples) + 1)

    print("\nSamples:")
    print("μ: %f" % samples_d.mean)
    print("σ: %f" % sqrt(samples_d.variance))

    print(list(unique_samples))

    # if len(unique_samples) > 1:
    #     samples_hist = relfreq(samples, numbins=len(unique_samples))
    #     d = list(zip(count(1), samples_hist.frequency))
    #     dd = dict(d)

    # Analyze sample bitstring lengths.
    bitstring_lengths = [len(r.bits) for r in records]
    bitstring_lengths_d = describe(bitstring_lengths)
    
    unique_bitstring_lengths = [*set(bitstring_lengths)]
    unique_bitstring_lengths.sort()

    # if len(unique_samples) > 1:
    #     bitstring_lengths_hist = relfreq(bitstring_lengths,
    #                                      numbins=len(unique_bitstring_lengths))
    #     freqs = bitstring_lengths_hist.frequency

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
