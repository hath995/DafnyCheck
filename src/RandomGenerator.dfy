
//https://prng.di.unimi.it/xoroshiro128plus.c
module RandomGenerator {
    // import opened Std.Collections.Seq

    function rotl(x: bv64, k: int): bv64
        requires 0 <= k < 64
    {
        (x << k) | (x >> (64 - k))
    }

    class XoroShift128Plus {
        var s0: bv64
        var s1: bv64

        constructor(s0: bv64, s1: bv64)
            ensures fresh(this)
        {
            this.s0 := s0;
            this.s1 := s1;
        }

        method clone() returns (c: XoroShift128Plus)
            ensures fresh(c)
        {
            c := new XoroShift128Plus(s0, s1);
        }

        method unsafeNext() returns (result: bv64)
            modifies this
        {
            var s0_ := s0;
            var s1_ := s1;
            result := s0 + s1;
            s1_ := s0 ^ s1;
            s0 := rotl(s0_, 24) ^ s1_ ^ (s1_ << 16);
            s1 := rotl(s1_, 37);
        }

        method next() returns (out: bv64, c: XoroShift128Plus)
            ensures fresh(c)
            ensures unchanged(this)
        {
            c := new XoroShift128Plus(s0, s1);
            out := c.unsafeNext();
        }        

        method nextReal() returns (out: real, c: XoroShift128Plus)
            ensures fresh(c)
            ensures unchanged(this)
        {
            c := new XoroShift128Plus(s0, s1);
            var n := c.unsafeNext();
            out := (n as real)/(MAX_LONG as real);
        }        

        method unsafeNextReal() returns (out: real)
            modifies this
        {
            var n := this.unsafeNext();
            out := (n as real)/(MAX_LONG as real);
        }        

        const JUMP: seq<bv64> := [0xdf900294d8f554a5, 0x170865df4b3201fc]
        const MAX_LONG: bv64 := 0xFFFFFFFFFFFFFFFF
        method unsafeJump() 
            modifies this
        {
            var s0_ := 0;
            var s1_ := 0;
            for i: int := 0 to 2 {
                for b: int := 0 to 64 {
                    if (JUMP[i] & (1 as bv64 << b as bv64)) != (0 as bv64) {
                        s0_ := s0_ ^ s0;
                        s1_ := s1_ ^ s1;
                    }
                    var _ := unsafeNext();
                }
            }
            s0 := s0_;
            s1 := s1_;
        }

        /* This is the jump function for the generator. It is equivalent
        to 2^64 calls to next(); it can be used to generate 2^64
        non-overlapping subsequences for parallel computations. -Blackman and Vigna */
        method jump() returns (c: XoroShift128Plus)
            ensures fresh(c)
            ensures unchanged(this)
        {
            c := new XoroShift128Plus(s0, s1);
            c.unsafeJump();
        }

        static method fromSeed(seed: bv64) returns (c: XoroShift128Plus)
            ensures fresh(c)
        {
            c := new XoroShift128Plus(!(seed), seed<<32);
        }


    }

    method {:test} reals() {
        var test := XoroShift128Plus.fromSeed(42);
        var te, re := test.nextReal();
        print(te);
        print(te < 0.9);
    }
}