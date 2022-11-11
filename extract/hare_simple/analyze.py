from collections import namedtuple

import csv
import numpy as np
import matplotlib.pyplot as plt
from math import sqrt
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

def analyze(records):

    print("# samples: %d" % len(records))

    # Analyze sample values.
    # samples = [int(r.sample) / 2 for r in records]
    # print(samples)
    # d = describe(samples)
    # samples_hist = relfreq(samples, numbins=2)
    # # print(samples_hist)

    # # Plot histogram distribution of bitstring lengths.
    # # plot(samples_hist, title='samples histogram', min_offset=0, max_offset=0)
    # plot(samples_hist)
    
    # # hist = relfreq(samples, numbins=2)
    # # print(hist)

    # # Analyze sample bitstrings.
    # bitstrings = [r.bits for r in records]
    # # print(bitstrings)

    # # hist = relfreq(bitstrings, numbins=10)

    # # Analyze sample bitstring lengths.
    bitstring_lengths = [len(r.bits) for r in records]
    unique_bitstring_lengths = [*set(bitstring_lengths)]
    unique_bitstring_lengths.sort()
    # # print(unique_bitstring_lengths)

    # # bitstring_lengths_hist = relfreq(bitstring_lengths,
    # #                                  numbins=len(unique_bitstring_lengths))
    # # print(bitstring_lengths_hist)

    bitstring_lengths_hist = relfreq(bitstring_lengths,
                                     numbins=len(unique_bitstring_lengths))
    freqs = bitstring_lengths_hist.frequency
    print(bitstring_lengths_hist)
    print(freqs)

    # Plot histogram distribution of bitstring lengths.
    # x = bitstring_lengths_hist.lowerlimit + \
    #     np.linspace(0, bitstring_lengths_hist.binsize *
    #                 bitstring_lengths_hist.frequency.size,
    #                 bitstring_lengths_hist.frequency.size)
    x = unique_bitstring_lengths
    
    print(x)
    fig = plt.figure()
    ax = fig.add_subplot(1, 1, 1)
    ax.bar(x, freqs, width=bitstring_lengths_hist.binsize * (4/5))
    ax.set_title('Geometric Sample Histogram, n=%d' % )
    ax.set_xlim([min(x) - .65, max(x) + 0.65])
    ax.set_xticks(x)
    ax.set_ylim([0, 1])
    # ax.bar_label(p1, label_type='center')
    for i in range(len(x)):
        plt.annotate("%.3f" % freqs[i], xy=(2 + i * 2, freqs[i]), ha='center', va='bottom')
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
    
    # num_true = 0
    # for o in records:
    #     if o['sample'] == '1':
    #         num_true += 1
    # print("num_true: %d" % num_true)
    # print("avg true: %f" % (num_true / len(records)))

with open('samples.dat', newline='') as csvfile:
     reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
     # records = [{ 'sample': row[0],
     #              'bits': row[1],
     #              'time': float(row[2]) } for row in reader]
     records = [Record(row[0], row[1], float(row[2])) for row in reader]
     analyze(records)
