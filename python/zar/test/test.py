from zarpy import seed, build_coin, build_die, flip_n, roll_n
from scipy.stats import describe

if __name__ == "__main__":
    seed()

    # p = 11/257 ≈ 0.042801556420233464
    build_coin((11, 257))
    samples = flip_n(100000)
    samples_d = describe(samples)
    print(samples_d)

    # n = 200
    build_die(200)
    samples = roll_n(100000)
    samples_d = describe(samples)
    print(samples_d)
