from collections import namedtuple
from math import factorial, sqrt

import csv
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from math import sqrt
from scipy.stats import cumfreq, describe, relfreq

Record = namedtuple('Record', 'sample bits time')
def comb(n, k):
    return factorial(n) / (factorial(k) * factorial(n - k))

# Negative binomial distribution wrt probability p. Geometric when
# r=1. Pr(X) = k
def pmf(k, p, r):
    # return comb(k + r - 1, r - 1) * (1 - p)**k * p**r
    return comb(k + r - 1, r - 1) * p**k * (1 - p)**r

# print(pmf(0, 1/2, 1))

def is_prime(n):
    if n == 1:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(sqrt(n)) + 1):
        if n % i == 0:
            return False
    return True

def primes():
    yield 2
    for n in range(3, 1000, 2):
        if is_prime(n):
            yield n

def nonprimes():
    for n in range(1000):
        if not is_prime(n):
            yield n

# print(list(nonprimes()))

p = 2/3
r = 1
norm = sum([pmf(i, p, r) for i in primes()])

# Condition on n <= k.
def cond_pmf(k):
    # return pmf(k, p, r) / (1 - sum([pmf(i, p, r) for i in range(n)]))
    return (pmf(k, p, r) / norm) if is_prime(k) else 0

print(cond_pmf(2))

def true_pmf(k):
    return cond_pmf(k)

# print([(i, true_pmf(i)) for i in range(1000)])
# print(sum([true_pmf(i) for i in range(1000)]))

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
    return sum(abs(p - true_pmf(i)) / (abs(p) + abs(true_pmf(i))) for i, p in d) \
        / len(d)

# Approximate Shannon entropy.
def entropy():
    return -sum([true_pmf(i) * log2(true_pmf(i)) for i in range(3, 1000)])

def rel_freqs(samples, unique_samples):
    return [len(list(filter(lambda x: x == k, samples))) / len(samples) for k in unique_samples]

# Dictionary lookup with default 0.
def lookup(key, d):
    return d.get(key) or 0

# true_d = [(i, true_pmf(i)) for i in primes()][:60]

support = list(primes())[:7]
labels = [str(n) for n in support]
values = [true_pmf(n) for n in support]
print(labels)
print(values)

fig = plt.figure(figsize = (7, 5))
# fig = plt.figure()
# fig, ax = plt.subplots(figsize=(7, 5))
# ax.axis('off')
plt.box(False)

# creating the bar plot
# plt.bar(labels, values, color ='maroon', width = 0.4)
# plt.xticks(labels)
plt.bar(labels, values)
 
plt.xlabel("Number of heads (h)")
plt.ylabel("Probability")
# plt.title("Students enrolled in different courses")
plt.show()

# def analyze(records):
#     global i
#     global t

#     print("# samples: %d" % len(records))

#     times = [r.time for r in records]

#     # Analyze sample values.
#     samples = [int(r.sample) for r in records]
#     unique_samples = range(min(samples), max(samples) + 1)
#     # unique_samples = [*set(samples)]
#     # unique_samples.sort()
#     print(len(samples))
#     print(unique_samples)

#     fig, ax = plt.subplots()

#     p = 1/6
#     n = 0
#     # true_dist = [pmf(x, p, 1) for x in unique_samples]
#     true_dist = [cond_pmf(x, p, 1, n) for x in unique_samples]

#     i, t = 0, 0
#     step = 100
#     def update(_):
#         global i, t
#         t += sum(times[i:i+step])
#         i += step
#         unique_samples = range(min(samples[:i+1]), max(samples[:i+1]) + 1)
#         samples_hist = relfreq(samples[:i+1], numbins=max(unique_samples)+1)

#         ixs = pred_ixs(lambda x: x >= 0.01, samples_hist.frequency)
#         # print(ixs)

#         freqs = [samples_hist.frequency[ix] for ix in ixs]
#         # freqs = list(filter(lambda x: x >= 0.01, samples_hist.frequency))
        
#         # unique_samples = unique_samples[:len(freqs)]
#         unique_samples = [unique_samples[ix] for ix in ixs]
#         print(unique_samples)
#         ax.clear()
        
#         # ax.bar(unique_samples,
#         #        true_dist[:len(freqs)],
#         #        width=samples_hist.binsize * (4/5),
#         #        alpha=0.5
#         # )
#         # ax.bar(unique_samples, freqs, width=samples_hist.binsize * (4/5), alpha=0.5)
#         # ax.set_title('Geometric Histogram, n=%d, p=1/6' % len(records))
#         # ax.set_xlim([min(unique_samples) -.65, max(unique_samples) + 0.65])
#         # ax.set_xticks(unique_samples)
#         # ax.set_ylim([0, max(freqs) + 0.05])
#         # for j in range(len(unique_samples)):
#         #     plt.annotate("%.3f" % freqs[j], xy=(j, freqs[j]), ha='center', va='bottom')

#         ax.bar(unique_samples,
#                true_dist[:len(freqs)],
#                width = 5 / len(freqs),
#                # width=samples_hist.binsize * (4/5),
#                color='black',
#                alpha=0.5
#         )
#         ax.bar(unique_samples,
#                freqs,
#                width = 10 / len(freqs),
#                # width=samples_hist.binsize * (4/5),
#                color='red',
#                alpha=0.5)
#         ax.set_title('Geometric Histogram, n=%d, p=%.2f' % (len(records), p))
#         # ax.set_xlim([min(unique_samples) - .65, max(unique_samples) + 0.65])
#         # ax.set_xlim([min(unique_samples) - 1, max(unique_samples) + 1])
#         ax.set_xticks(unique_samples)
#         ax.set_ylim([0, max(freqs) + 0.05])
#         for j in range(len(unique_samples)):
#             plt.annotate("%.2f" % freqs[j],
#                          # xy=(j, max(freqs[j], pmf(unique_samples[j], p, 1))),
#                          xy=(j, max(freqs[j], cond_pmf(unique_samples[j], p, 1, n))),
#                          ha='center', va='bottom')
            
#         ax.set_title("n = %d, t = %f" % (i, t))
    
#     ani = FuncAnimation(fig, update, interval=1000/12,
#                         frames = int(len(samples) / step) - 1, repeat=False)
#     plt.show()


# with open('samples100k.dat', newline='') as csvfile:
#      reader = csv.reader(csvfile, delimiter=' ', quotechar='|')
#      records = [Record(row[0], row[1], float(row[2])) for row in reader]
#      analyze(records)
