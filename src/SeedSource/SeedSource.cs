// C# implementation of SeedSource.GetSeed (bv64 -> ulong).
// Build/run:  dafny run --target:cs SeedSourceDemo.dfy --input SeedSource.cs
using System;

namespace SeedSource {
  public partial class __default {
    public static ulong GetSeed() {
      var bytes = new byte[8];
      System.Security.Cryptography.RandomNumberGenerator.Fill(bytes);
      return BitConverter.ToUInt64(bytes, 0);
    }

    // Monotonic nanoseconds, from the high-resolution Stopwatch clock (only
    // differences are consumed, so the origin is unspecified). Scaling ticks by
    // ns/tick through a double is exact enough for durations.
    public static ulong NowNanos() {
      return (ulong)(System.Diagnostics.Stopwatch.GetTimestamp() *
                     (1_000_000_000.0 / System.Diagnostics.Stopwatch.Frequency));
    }
  }
}
