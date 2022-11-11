from collections import namedtuple

import csv
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from math import sqrt
from scipy.stats import cumfreq, describe, relfreq

Record = namedtuple('Record', 'sample bits time')

def analyze(records):
    global i
    global t

    print("# samples: %d" % len(records))

    # Analyze sample values.
    samples = [int(r.sample) / 2 for r in records]
    times = [r.time for r in records]
    print(len(samples))
    # d = describe(samples)
    # samples_hist = relfreq(samples, numbins=2)
    # print(samples_hist)

    # Plot histogram distribution of bitstring lengths.
    # plot(samples_hist, title='samples histogram', min_offset=0, max_offset=0)
    # plot(samples_hist)

    fig, ax = plt.subplots()

    i, t = 0, 0
    step = 10
    def update(num):
        global i, t
        # i = min([len(samples) - 1, i + 100])
        t += sum(times[i:i+step])
        i += step
        # print(len(samples))
        # print(i)
        hist = relfreq(samples[:i], numbins=2)
        ax.clear()
        ax.pie(hist.frequency,
               labels=[False, True],
               startangle=270,
               explode=[0.05, 0.05],
               colors=["darkred", "#005DAA"],
               autopct=lambda x: '%.3f' % (x / 100)
        )
        ax.set_title("n = %d, t = %f" % (i, t))

    # ani = FuncAnimation(fig, update, frames=range(100), repeat=False)
    # ani = FuncAnimation(fig, update, interval=30, frames=int(len(samples)/step), repeat=True)
    # ani = FuncAnimation(fig, update, interval=30, repeat=True)
    ani = FuncAnimation(fig, update, interval=1000/24, repeat=True) 
    plt.show()
    
    # hist = relfreq(samples, numbins=2)
    # print(hist)


with open('samples.dat', newline='') as csvfile:
     reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
     records = [Record(row[0], row[1], float(row[2])) for row in reader]
     analyze(records)
