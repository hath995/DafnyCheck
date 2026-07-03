# Python implementation of SeedSource.GetSeed / NowNanos.
# Build/run:  dafny run --target:py SeedSourceDemo.dfy --input SeedSource.py
import secrets
import time


class default__:
    @staticmethod
    def GetSeed():
        return secrets.randbits(64)

    # Monotonic nanoseconds; only differences are consumed, origin unspecified.
    @staticmethod
    def NowNanos():
        return time.perf_counter_ns()
