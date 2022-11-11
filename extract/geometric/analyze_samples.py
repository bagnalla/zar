from collections import namedtuple
from itertools import takewhile

import csv
import numpy as np
import matplotlib.pyplot as plt
from math import factorial, sqrt
from scipy.stats import cumfreq, describe, relfreq

Record = namedtuple('Record', 'sample bits time')

# def mk_bins(data):
#     bins = {}
#     for d in data:
#         if d in bins:
#             bins[d] += 1
#         else:
#             bins[d] = 1

# def plot(hist):
#     plt.pie(hist.frequency,
#             labels=[False, True],
#             startangle=270,
#             explode=[0.05, 0.05],
#             colors=["darkred", "#005DAA"],
#             autopct=lambda x: '%.2f' % (x / 100)
#     )
#     plt.show()
    
# def plot(hist, title='Relative frequency histogram', min_offset=0, max_offset=0):
#     # x = hist.lowerlimit + \
#     #     np.linspace(0, hist.binsize * hist.frequency.size, hist.frequency.size)
#     x = np.array([False, True])
#     print(hist)
#     print("x: " + str(x))
#     fig = plt.figure()
#     ax = fig.add_subplot(1, 1, 1)
#     # ax.bar(x, hist.frequency, width=hist.binsize)
#     ax.bar(x, hist.frequency, width=.5)
#     ax.set_xticks([False, True])
#     # ax.set_title(title)
#     # ax.set_xlim([-1, 2])
#     ax.set_xscale(1)
#     ax.set_ylim([0, 1])
#     # ax.set_xlim([x.min() - min_offset, x.max() + max_offset])
#     plt.show()

def comb(n, k):
    return factorial(n) / (factorial(k) * factorial(n - k))

# Negative binomial distribution. Geometric is when r=1.
# Pr(X) = k
def pmf(k, p, r):
    return comb(k + r - 1, r - 1) * (1 - p)**k * p**r

def analyze(records):
    print("# samples: %d" % len(records))

    print(pmf(1, 1/6, 1))

    # Analyze sample values.
    samples = [int(r.sample) for r in records]
    unique_samples = range(min(samples), max(samples) + 1)
    # unique_samples = [*set(samples)]
    # unique_samples.sort()
    # print(samples)

    samples_hist = relfreq(samples, numbins=len(unique_samples))
    # freqs = samples_hist.frequency
    freqs = list(takewhile(lambda x: x >= 0.01, samples_hist.frequency))
    unique_samples = unique_samples[:len(freqs)]
    
    fig = plt.figure()

    # bx = fig.add_subplot(1, 1, 1)
    # bx.bar(unique_samples, [pmf(x, 1/6, 1) for x in unique_samples],
    #        width=samples_hist.binsize * (4/5))
    # # ax.set_xlim([min(unique_samples) - .65, max(unique_samples) + 0.65])
    # ax.set_xlim([min(unique_samples) -.65, max(unique_samples[0:33]) + 0.65])
    # ax.set_xticks(unique_samples[0:33])
    # ax.set_ylim([0, max(freqs) + 0.05])
    # # ax.bar_label(p1, label_type='center')

    p = 1/6
    true_dist = [pmf(x, p, 1) for x in unique_samples]

    ax = fig.add_subplot(1, 1, 1)
    
    ax.bar(unique_samples,
           true_dist,
           width=samples_hist.binsize * (4/5),
           color='black',
           alpha=0.5
    )
    ax.bar(unique_samples,
           freqs,
           width=samples_hist.binsize * (4/5),
           color='red',
           alpha=0.5)
    ax.set_title('Geometric Histogram, n=%d, p=%.2f' % (len(records), p))
    ax.set_xlim([min(unique_samples) -.65, max(unique_samples) + 0.65])
    ax.set_xticks(unique_samples)
    ax.set_ylim([0, max(freqs) + 0.05])
    for i in range(len(unique_samples)):
        plt.annotate("%.2f" % freqs[i],
                     xy=(i, max(freqs[i], pmf(unique_samples[i], p, 1))),
                     ha='center', va='bottom')
        
    plt.show()

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

with open('samples10k.dat', newline='') as csvfile:
     reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
     records = [Record(row[0], row[1], float(row[2])) for row in reader]
     analyze(records)
