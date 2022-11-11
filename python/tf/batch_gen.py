# A class for generating minibatches. Uses sampling without
# replacement. Returns batches of indices for each minibatch.

import numpy as np
from itertools import cycle, islice
from uniform import seed, build, single, many

class batch_gen(object):
    def __init__(self, batch_size, num_indices, replace=False,
                 num_batches=-1, buf_size=-1):
        self.batch_size = batch_size
        self.num_indices = num_indices
        self.num_batches = num_batches
        self.counter = 0
        self.replace = replace

        if buf_size > 0:
            self.buf_size = buf_size
        else:
            self.buf_size = self.num_indices
            
        # initialize rng
        seed()

        if self.replace:
            build(self.num_indices)
        else:
            build(self.buf_size)
            self.stream = cycle(range(num_indices))
            self.buf = list(islice(self.stream, 0, self.buf_size))

    def __iter__(self):
        return self

    def __next__(self):
        return self.next()

    def next(self):
        self.counter += 1
        if self.num_batches >= 0 and self.counter > self.num_batches:
            raise StopIteration()
        if self.replace:
            return many(self.batch_size)
            # return self.indices[[single() for _ in range(self.batch_size)]]
            # return np.random.choice(self.indices, self.batch_size, replace=True)
        else:
            batch = []
            for i in many(self.batch_size):
                batch.append(self.buf[i])
                del self.buf[i]
                self.buf.append(next(self.stream))

            # print("buf: " + str(self.buf))
            # print("batch: " + str(batch))
            return batch
