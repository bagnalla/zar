from zarpy import seed, build, single, many
from itertools import count, takewhile
import math
from math import sqrt
import timeit
import numpy as np
from scipy.stats import cumfreq, describe, relfreq

# def profile(n=10_000, depth=5):
#     t = timeit.Timer(lambda: evaluate(random_expr(depth))).timeit(n) / n
#     t_ = timeit.Timer(lambda: evaluate_(random_expr_(depth))).timeit(n) / n
#     t_bis = timeit.Timer(lambda: evaluate_bis(random_expr(depth))).timeit(n) / n
#     print(f"Bis     {t_bis*1e6:4.0f}us")
#     print(f"Normal  {t*1e6:4.0f}us")
#     print(f"Capsule {t_*1e6:4.0f}us")

N = 200

def pmf(k):
    return 1 / N if 0 <= k and k < N else 0

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

def lookup(key, d):
    return d.get(key) or 0

if __name__ == "__main__":
    seed()
    build(N)
    
    samples = many(100000)
    # print(samples)

    samples_d = describe(samples)
    unique_samples = range(min(samples), max(samples) + 1)
    true_d = list(takewhile(lambda x: x[1] > 0, ((i, pmf(i)) for i in count(1))))

    print("μ: %f" % samples_d.mean)
    print("σ: %f" % sqrt(samples_d.variance))

    samples_hist = relfreq(samples, numbins=len(unique_samples))
    d = list(zip(count(1), samples_hist.frequency))
    dd = dict(d)
    print("total variation distance: %f" % total_variation(dd, true_d))
    print("KL divergence: %f" % KL(dd, true_d))
    print("SMAPE: %f" % smape(d))

    # samples = [single(10000 - i, True) for i in range(200)]
    # print(samples)
    # for _ in range(10):
    #     print(single(0, 1, 1))
