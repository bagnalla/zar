# Zar: formally verified-correct n-sided die roller.

`import zarpy` to use the package.

`seed()` initializes the PRNG.

`build(n)` builds and caches an n-sided die to be used by subsequent calls for generating samples.

`single()` produces a single sample using the cached sampler.

`many(n)` produces n samples using the cached sampler.

`many_entropy(n)` produces n (x, b) pairs where x is a sample and b is the number of uniform random bits used to obtain x.