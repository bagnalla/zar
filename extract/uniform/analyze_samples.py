from collections import namedtuple
from itertools import takewhile
from math import comb

import csv
import numpy as np
import matplotlib.pyplot as plt
from math import sqrt
from scipy.stats import cumfreq, describe, relfreq

Record = namedtuple('Record', 'sample bits time')

def analyze(records):
    print("# samples: %d" % len(records))

    # Analyze sample values.
    samples = [int(r.sample) for r in records]
    unique_samples = range(min(samples), max(samples) + 1)
    # unique_samples = [*set(samples)]
    # unique_samples.sort()
    # print(samples)

    # # Analyze sample bitstring lengths.
    bitstring_lengths = [len(r.bits) for r in records]
    bitstring_lengths_d = describe(bitstring_lengths)
    
    unique_bitstring_lengths = [*set(bitstring_lengths)]
    unique_bitstring_lengths.sort()
    print(unique_bitstring_lengths)

    bitstring_lengths_hist = relfreq(bitstring_lengths,
                                     numbins=len(unique_bitstring_lengths))
    freqs = bitstring_lengths_hist.frequency
    # print(bitstring_lengths_hist)
    print(freqs)

    print("\nBits:")
    print("μ: %f" % bitstring_lengths_d.mean)
    print("σ: %f" % sqrt(bitstring_lengths_d.variance))
    print("Σ: %f" % sum(bitstring_lengths))


    samples_hist = relfreq(samples, numbins=len(unique_samples))
    # freqs = samples_hist.frequency
    freqs = list(takewhile(lambda x: x >= 0.01, samples_hist.frequency))
    unique_samples = unique_samples[:len(freqs)]

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

with open('samples.dat', newline='') as csvfile:
     reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
     records = [Record(row[0], row[1], float(row[2])) for row in reader]
     analyze(records)
