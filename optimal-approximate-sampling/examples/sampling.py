#!/usr/bin/env python

"""Example of finding optimal distribution given a fixed precision."""

import csv
import time
from tempfile import NamedTemporaryFile
from fractions import Fraction
from collections import Counter

from optas.divergences import KERNELS
from optas.opt import get_optimal_probabilities
from optas.construct import construct_sample_ky_encoding
from sample import sample_ky_encoding

from optas.writeio import write_sample_ky_encoding

start = time.time()

# Target probability distribution.
p_target = [Fraction(1, 200) for _ in range(200)]

# Obtain optimal probabilities (Algorithm 3).
precision = 32
kernel = 'hellinger'

# print("Calculating optimal probabilities...")

p_approx = get_optimal_probabilities(2**precision, p_target, KERNELS[kernel])

# print("Building sampler...")

# Construct the sampler (Section 5).
enc, n, k = construct_sample_ky_encoding(p_approx)

# print("Running sampler...")

end = time.time()

print('setup time: %fs' % (end - start))

start = time.time()

# Run the sampler.
num_samples = 100000
samples_bits = [sample_ky_encoding(enc) for _i in range(num_samples)]
# counts = Counter(samples)

end = time.time()

print('sample time: %fs' % (end - start))

# f_expect = [float(p) for p in p_target]
# f_actual = [counts[i]/num_samples for i in sorted(counts.keys())]

# print('generated %d samples' % (num_samples,))
# print('average frequencies: %s' % (f_expect,))
# print('sampled frequencies: %s' % (f_actual,))

# print(samples_bits)

# Dump sample records to file.
with open('optas_python_samples.dat', 'w', newline='') as csvfile:
    writer = csv.writer(csvfile, delimiter=' ',
                        quotechar='|', quoting=csv.QUOTE_MINIMAL)
    [writer.writerow((n-1, b)) for n, b in samples_bits]


# Write sampler to disk (for the C command-line interface).
with NamedTemporaryFile(delete=False) as f:
    write_sample_ky_encoding(enc, n, k, f.name)
    print('\nsampler written to: %s' % (f.name,))
    print('to generate %d samples in C, run this command from c/ directory:'
        % (num_samples,))
    print('$ ./mainc.opt 1 %d ky.enc %s' % (num_samples, f.name))
