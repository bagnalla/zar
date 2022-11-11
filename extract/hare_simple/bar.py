from collections import namedtuple
# from itertools import takewhile
from math import comb

import csv
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from math import sqrt
from scipy.stats import cumfreq, describe, relfreq

Record = namedtuple('Record', 'sample bits time')

def fst(p): return p[0]
def snd(p): return p[1]

def pred_ixs(pred, l):
    return list(map(fst, filter(lambda x: pred(x[1]), enumerate(l))))

def analyze(records):
    global i
    global t

    print("# samples: %d" % len(records))

    times = [r.time for r in records]

    # Analyze sample values.
    samples = [int(r.sample) for r in records]
    unique_samples = range(min(samples), max(samples) + 1)
    # unique_samples = [*set(samples)]
    # unique_samples.sort()
    print(len(samples))
    print(unique_samples)

    fig, ax = plt.subplots()

    p = 1/6
    n = 0

    i, t = 0, 0
    step = 100
    def update(_):
        global i, t
        t += sum(times[i:i+step])
        i += step
        unique_samples = range(min(samples[:i+1]), max(samples[:i+1]) + 1)
        samples_hist = relfreq(samples[:i+1], numbins=max(unique_samples)+1)

        # ixs = pred_ixs(lambda x: x >= 0.01, samples_hist.frequency)
        # # print(ixs)

        # freqs = [samples_hist.frequency[ix] for ix in ixs]
        # # freqs = list(filter(lambda x: x >= 0.01, samples_hist.frequency))
        freqs = samples_hist.frequency
        
        # # unique_samples = unique_samples[:len(freqs)]
        # unique_samples = [unique_samples[ix] for ix in ixs]
        # print(unique_samples)
        # print(freqs)
        # ax.clear()
        
        # ax.bar(unique_samples,
        #        true_dist[:len(freqs)],
        #        width=samples_hist.binsize * (4/5),
        #        alpha=0.5
        # )
        # ax.bar(unique_samples, freqs, width=samples_hist.binsize * (4/5), alpha=0.5)
        # ax.set_title('Geometric Histogram, n=%d, p=1/6' % len(records))
        # ax.set_xlim([min(unique_samples) -.65, max(unique_samples) + 0.65])
        # ax.set_xticks(unique_samples)
        # ax.set_ylim([0, max(freqs) + 0.05])
        # for j in range(len(unique_samples)):
        #     plt.annotate("%.3f" % freqs[j], xy=(j, freqs[j]), ha='center', va='bottom')

        ax.bar(unique_samples,
               freqs,
               # width = 10 / len(freqs),
               width=samples_hist.binsize * (4/5),
               color='red',
               alpha=0.5)
        ax.set_title('Geometric Histogram, n=%d, p=%.2f' % (len(records), p))
        # ax.set_xlim([min(unique_samples) - .65, max(unique_samples) + 0.65])
        # ax.set_xlim([min(unique_samples) - 1, max(unique_samples) + 1])
        ax.set_xticks(unique_samples)
        ax.set_ylim([0, max(freqs) + 0.05])
        for j in range(len(unique_samples)):
            plt.annotate("%.2f" % freqs[j],
                         xy=(j, freqs[j]),
                         ha='center', va='bottom')
            
        ax.set_title("n = %d, t = %f" % (i, t))
    
    ani = FuncAnimation(fig, update, interval=1000/12,
                        frames = int(len(samples) / step) - 1, repeat=False)
    plt.show()
    
    # hist = relfreq(samples, numbins=2)
    # print(hist)


with open('samples.dat', newline='') as csvfile:
     reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
     records = [Record(row[0], row[1], float(row[2])) for row in reader]
     analyze(records)
