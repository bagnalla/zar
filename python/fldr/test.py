import csv
import time
from fldr import fldr_preprocess_int, fldr_sample
# from uniform import seed, build, single, many

start = time.time()
N_sample = 100000
distribution = [1 for _ in range(200)]
x = fldr_preprocess_int(distribution)
end = time.time()

print('setup time: %fs' % (end - start))

start = time.time()
# Generate sample records.
samples_bits = [fldr_sample(x) for _i in range(N_sample)]
end = time.time()

print('sample time: %fs' % (end - start))

# Dump sample records to file.
with open('fldr_python_samples.dat', 'w', newline='') as csvfile:
    writer = csv.writer(csvfile, delimiter=' ',
                        quotechar='|', quoting=csv.QUOTE_MINIMAL)
    [writer.writerow(x) for x in samples_bits]


# seed()
# build(200)
# samples2 = many(100000)
# # print(samples2)
