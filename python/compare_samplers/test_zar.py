import csv
import time
from zar import seed, build, single, many_entropy

start = time.time()
seed()
build(200)
end = time.time()

print('setup time: %fs' % (end - start))

start = time.time()
# Generate sample records.
samples_bits = many_entropy(100000)
end = time.time()

print('sample time: %fs' % (end - start))

# Dump sample records to file.
with open('zar_python_samples.dat', 'w', newline='') as csvfile:
    writer = csv.writer(csvfile, delimiter=' ',
                        quotechar='|', quoting=csv.QUOTE_MINIMAL)
    [writer.writerow(x) for x in samples_bits]
