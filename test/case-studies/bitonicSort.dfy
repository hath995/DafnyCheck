// ============================================================================
// Bitonic sort, verified via the 0-1 principle.
//
//   bitonicSort : sorts any power-of-two-length seq<int>, multiset-preserving.
//
// Copied verbatim from Algorithms/bitonicSort.dfy as a case study for the
// DafnyCheck property-based testing framework; the ONLY change is the wrapping
// `module BitonicSort { ... }` so the test file can `import opened BitonicSort`.
//
// Structure:
//   * bitonicMerge is a TOTAL function (precondition: power-of-two length),
//     proven length- and multiset-preserving.  Sortedness is a separate lemma.
//   * bitonic(s) := some rotation of s is unimodal (ascending then descending);
//     this is the correct cyclic definition (the old midpoint-split predicate
//     was too weak -- it rejected monotone halves that the half-cleaner emits).
//   * mergeSorts proves sortedAsc(bitonicMerge(s)) for bitonic s via the 0-1
//     principle: clamp (threshold) commutes with the comparator network, clamp
//     preserves bitonicity, and sortedness of all thresholdings implies
//     sortedness.  So it suffices to sort 0-1 bitonic inputs (merge01Sorts).
//
// One classical fact is assumed as an axiom: HalfCleaner01 (see below).
// ============================================================================
module BitonicSort {

predicate sortedAsc(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate sortedDesc(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] >= s[j]
}

function natPow(n: nat, k: nat): nat {
    if k == 0 then 1 else if k == 1 then n else n*natPow(n, k-1)
}

ghost predicate IsPowerOfTwo(n: nat)
{
    exists k :: k >= 0 && n == natPow(2, k)
}

function min(a: int, b: int): int { if a <= b then a else b }
function max(a: int, b: int): int { if a >= b then a else b }

// ---- helper: a power of two > 1 has a power-of-two half ----
lemma HalfIsPowerOfTwo(m: nat)
    requires IsPowerOfTwo(m) && m > 1
    ensures IsPowerOfTwo(m / 2) && 2 * (m / 2) == m
{
    var k :| k >= 0 && m == natPow(2, k);
    assert k >= 1;
    assert m == 2 * natPow(2, k - 1);
}

// ===== Total bitonic merge (half-cleaner recursion) =====
// No bitonic precondition, no sortedness postcondition: just structure + multiset.
function bitonicMerge(s: seq<int>): seq<int>
    requires |s| == 0 || IsPowerOfTwo(|s|)
    ensures |bitonicMerge(s)| == |s|
    ensures multiset(bitonicMerge(s)) == multiset(s)
    decreases |s|
{
    if |s| <= 1 then s
    else
        var n := |s| / 2;
        HalfIsPowerOfTwo(|s|);
        assert |s[n..]| == n;
        var mins := seq(n, i requires 0 <= i < n => min(s[i], s[i + n]));
        var maxs := seq(n, i requires 0 <= i < n => max(s[i], s[i + n]));
        MultisetMerge(s, n, mins, maxs);
        bitonicMerge(mins) + bitonicMerge(maxs)
}

// ---- multiset preservation of the half-cleaner step ----
lemma MinMaxPair(x: int, y: int)
    ensures multiset([min(x, y), max(x, y)]) == multiset([x, y])
{
}

lemma ZipMinMax(a: seq<int>, b: seq<int>, lo: seq<int>, hi: seq<int>)
    requires |a| == |b| == |lo| == |hi|
    requires forall i :: 0 <= i < |a| ==> lo[i] == min(a[i], b[i])
    requires forall i :: 0 <= i < |a| ==> hi[i] == max(a[i], b[i])
    ensures multiset(lo) + multiset(hi) == multiset(a) + multiset(b)
    decreases |a|
{
    if |a| == 0 {
    } else {
        var m := |a|;
        ZipMinMax(a[..m-1], b[..m-1], lo[..m-1], hi[..m-1]);
        assert a == a[..m-1] + [a[m-1]];
        assert b == b[..m-1] + [b[m-1]];
        assert lo == lo[..m-1] + [lo[m-1]];
        assert hi == hi[..m-1] + [hi[m-1]];
        MinMaxPair(a[m-1], b[m-1]);
        calc {
            multiset(lo) + multiset(hi);
            multiset(lo[..m-1]) + multiset([lo[m-1]]) + multiset(hi[..m-1]) + multiset([hi[m-1]]);
            (multiset(lo[..m-1]) + multiset(hi[..m-1])) + (multiset([lo[m-1]]) + multiset([hi[m-1]]));
            (multiset(a[..m-1]) + multiset(b[..m-1])) + (multiset([a[m-1]]) + multiset([b[m-1]]));
            multiset(a) + multiset(b);
        }
    }
}

lemma MultisetMerge(s: seq<int>, n: nat, mins: seq<int>, maxs: seq<int>)
    requires 2 * n == |s|
    requires |mins| == n && |maxs| == n
    requires forall i :: 0 <= i < n ==> mins[i] == min(s[i], s[i + n])
    requires forall i :: 0 <= i < n ==> maxs[i] == max(s[i], s[i + n])
    ensures multiset(mins) + multiset(maxs) == multiset(s)
{
    assert |s[n..]| == n;
    assert forall i :: 0 <= i < n ==> mins[i] == min(s[0..n][i], s[n..][i]);
    assert forall i :: 0 <= i < n ==> maxs[i] == max(s[0..n][i], s[n..][i]);
    ZipMinMax(s[0..n], s[n..], mins, maxs);
    assert s == s[0..n] + s[n..];
}

// ===== 0-1 principle plumbing =====

// Threshold map: 1 where s[i] >= t, else 0.  Monotone in s[i].
function clamp(s: seq<int>, t: int): seq<int>
    ensures |clamp(s, t)| == |s|
    ensures forall i :: 0 <= i < |s| ==> clamp(s, t)[i] == (if s[i] >= t then 1 else 0)
{
    seq(|s|, i requires 0 <= i < |s| => if s[i] >= t then 1 else 0)
}

predicate is01(s: seq<int>) { forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1 }

lemma ClampIs01(s: seq<int>, t: int)
    ensures is01(clamp(s, t))
{
}

// clamp commutes with the comparator (monotonicity of thresholding).
lemma ClampMinMax(x: int, y: int, t: int)
    ensures (if min(x, y) >= t then 1 else 0) == min(if x >= t then 1 else 0, if y >= t then 1 else 0)
    ensures (if max(x, y) >= t then 1 else 0) == max(if x >= t then 1 else 0, if y >= t then 1 else 0)
{
}

lemma ClampConcat(a: seq<int>, b: seq<int>, t: int)
    ensures clamp(a + b, t) == clamp(a, t) + clamp(b, t)
{
    assert |clamp(a + b, t)| == |clamp(a, t) + clamp(b, t)|;
    forall i | 0 <= i < |a + b|
        ensures clamp(a + b, t)[i] == (clamp(a, t) + clamp(b, t))[i]
    {
        if i < |a| {
            assert (a + b)[i] == a[i];
        } else {
            assert (a + b)[i] == b[i - |a|];
        }
    }
}

// The merge commutes with clamp:  merge(clamp(s)) == clamp(merge(s)).
lemma MergeClampCommute(s: seq<int>, t: int)
    requires |s| == 0 || IsPowerOfTwo(|s|)
    ensures bitonicMerge(clamp(s, t)) == clamp(bitonicMerge(s), t)
    decreases |s|
{
    if |s| <= 1 {
        // both sides equal clamp(s, t)
    } else {
        var n := |s| / 2;
        HalfIsPowerOfTwo(|s|);
        var cs := clamp(s, t);
        assert |cs| == |s| && |cs| / 2 == n;

        var mins  := seq(n, i requires 0 <= i < n => min(s[i], s[i + n]));
        var maxs  := seq(n, i requires 0 <= i < n => max(s[i], s[i + n]));
        var cmins := seq(n, i requires 0 <= i < n => min(cs[i], cs[i + n]));
        var cmaxs := seq(n, i requires 0 <= i < n => max(cs[i], cs[i + n]));

        // clamp of mins == mins of clamp, pointwise (monotonicity).
        forall i | 0 <= i < n
            ensures cmins[i] == clamp(mins, t)[i]
            ensures cmaxs[i] == clamp(maxs, t)[i]
        {
            ClampMinMax(s[i], s[i + n], t);
        }
        assert cmins == clamp(mins, t);
        assert cmaxs == clamp(maxs, t);

        MergeClampCommute(mins, t);
        MergeClampCommute(maxs, t);

        // assemble
        calc {
            bitonicMerge(cs);
            bitonicMerge(cmins) + bitonicMerge(cmaxs);
            bitonicMerge(clamp(mins, t)) + bitonicMerge(clamp(maxs, t));
            clamp(bitonicMerge(mins), t) + clamp(bitonicMerge(maxs), t);
            { ClampConcat(bitonicMerge(mins), bitonicMerge(maxs), t); }
            clamp(bitonicMerge(mins) + bitonicMerge(maxs), t);
            clamp(bitonicMerge(s), t);
        }
    }
}

// If every threshold view is sorted, the sequence is sorted (0-1 principle, easy half).
lemma SortedViaClamp(s: seq<int>)
    requires forall t :: sortedAsc(clamp(s, t))
    ensures sortedAsc(s)
{
    forall i, j | 0 <= i < j < |s|
        ensures s[i] <= s[j]
    {
        var t := s[i];
        assert sortedAsc(clamp(s, t));
        assert clamp(s, t)[i] == 1;
        assert clamp(s, t)[j] >= clamp(s, t)[i];
        assert clamp(s, t)[j] == 1;
    }
}

// ===== Correct bitonic definition: a rotation that is unimodal (asc then desc) =====
function rotate(s: seq<int>, r: nat): seq<int>
    requires 0 <= r <= |s|
    ensures |rotate(s, r)| == |s|
{
    s[r..] + s[..r]
}

predicate unimodal(s: seq<int>)
{
    exists p :: 0 <= p <= |s| && sortedAsc(s[..p]) && sortedDesc(s[p..])
}

predicate bitonic(s: seq<int>)
{
    exists r :: 0 <= r <= |s| && unimodal(rotate(s, r))
}

// ---- clamp preserves bitonicity ----
lemma ClampSorted(u: seq<int>, t: int)
    ensures sortedAsc(u) ==> sortedAsc(clamp(u, t))
    ensures sortedDesc(u) ==> sortedDesc(clamp(u, t))
{
}

lemma ClampPrefix(u: seq<int>, t: int, p: int)
    requires 0 <= p <= |u|
    ensures clamp(u, t)[..p] == clamp(u[..p], t)
    ensures clamp(u, t)[p..] == clamp(u[p..], t)
{
}

lemma ClampUnimodal(u: seq<int>, t: int)
    requires unimodal(u)
    ensures unimodal(clamp(u, t))
{
    var p :| 0 <= p <= |u| && sortedAsc(u[..p]) && sortedDesc(u[p..]);
    ClampPrefix(u, t, p);
    ClampSorted(u[..p], t);
    ClampSorted(u[p..], t);
    assert sortedAsc(clamp(u, t)[..p]) && sortedDesc(clamp(u, t)[p..]);
}

lemma ClampRotate(s: seq<int>, r: nat, t: int)
    requires 0 <= r <= |s|
    ensures clamp(rotate(s, r), t) == rotate(clamp(s, t), r)
{
    ClampConcat(s[r..], s[..r], t);
    ClampPrefix(s, t, r);
}

lemma ClampPreservesBitonic(s: seq<int>, t: int)
    requires bitonic(s)
    ensures bitonic(clamp(s, t))
{
    var r :| 0 <= r <= |s| && unimodal(rotate(s, r));
    ClampUnimodal(rotate(s, r), t);
    ClampRotate(s, r, t);
    assert unimodal(rotate(clamp(s, t), r));
}

// ===== Sorting proof (0-1 core + lift) =====

// Concatenate two sorted runs where everything in the first <= everything in the second.
lemma ConcatSorted(L: seq<int>, R: seq<int>)
    requires sortedAsc(L) && sortedAsc(R)
    requires forall a, b :: a in L && b in R ==> a <= b
    ensures sortedAsc(L + R)
{
    forall i, j | 0 <= i < j < |L + R|
        ensures (L + R)[i] <= (L + R)[j]
    {
        if i < |L| && j < |L| {
        } else if i >= |L| && j >= |L| {
            assert (L + R)[i] == R[i - |L|];
            assert (L + R)[j] == R[j - |L|];
        } else {
            assert (L + R)[i] == L[i] && L[i] in L;
            assert (L + R)[j] == R[j - |L|] && R[j - |L|] in R;
        }
    }
}

// ============================================================================
// AXIOM (the one unproven fact): Batcher's half-cleaner lemma, 0-1 case.
//
// For a 0-1 *bitonic* sequence s of length 2n, the element-wise comparison of
// the two halves (mins[i]=min(s[i],s[i+n]), maxs[i]=max(s[i],s[i+n])) yields:
//   (1) two bitonic half-sequences (so the recursion's precondition holds), and
//   (2) every element of mins <= every element of maxs (the "clean" property,
//       so that sorted(mins) ++ sorted(maxs) is itself sorted).
//
// This is the classical, well-known combinatorial heart of Batcher's network.
// A full Dafny proof is a self-contained ~150-200 line exercise: characterize a
// 0-1 bitonic sequence as having its 1s on a contiguous cyclic interval, then
// do the interval/antipodal-pairing case analysis on the 1-block boundaries.
// Everything ELSE in this file (the 0-1 principle reduction, clamp/comparator
// commutation, multiset preservation, the sorting lift, and the recursion) is
// fully proven against this single assumption.
// ============================================================================
lemma {:axiom} HalfCleaner01(s: seq<int>, n: nat, mins: seq<int>, maxs: seq<int>)
    requires 2 * n == |s| && n >= 1
    requires is01(s) && bitonic(s)
    requires |mins| == n && |maxs| == n
    requires forall i :: 0 <= i < n ==> mins[i] == min(s[i], s[i + n])
    requires forall i :: 0 <= i < n ==> maxs[i] == max(s[i], s[i + n])
    ensures bitonic(mins) && bitonic(maxs)
    ensures forall a, b :: a in mins && b in maxs ==> a <= b

lemma merge01Sorts(s: seq<int>)
    requires |s| == 0 || IsPowerOfTwo(|s|)
    requires is01(s) && bitonic(s)
    ensures sortedAsc(bitonicMerge(s))
    decreases |s|
{
    if |s| <= 1 {
    } else {
        var n := |s| / 2;
        HalfIsPowerOfTwo(|s|);
        var mins := seq(n, i requires 0 <= i < n => min(s[i], s[i + n]));
        var maxs := seq(n, i requires 0 <= i < n => max(s[i], s[i + n]));
        assert is01(mins) && is01(maxs);
        HalfCleaner01(s, n, mins, maxs);

        merge01Sorts(mins);
        merge01Sorts(maxs);
        var L := bitonicMerge(mins);
        var R := bitonicMerge(maxs);
        // cross property carries through the multiset-preserving merge
        assert forall a, b :: a in L && b in R ==> a <= b by {
            forall a, b | a in L && b in R
                ensures a <= b
            {
                assert a in multiset(L) && multiset(L) == multiset(mins);
                assert b in multiset(R) && multiset(R) == multiset(maxs);
                assert a in mins && b in maxs;
            }
        }
        ConcatSorted(L, R);
        assert bitonicMerge(s) == L + R;
    }
}

// Lift to integers via the 0-1 principle.
lemma mergeSorts(s: seq<int>)
    requires |s| == 0 || IsPowerOfTwo(|s|)
    requires bitonic(s)
    ensures sortedAsc(bitonicMerge(s))
{
    forall t
        ensures sortedAsc(clamp(bitonicMerge(s), t))
    {
        MergeClampCommute(s, t);
        ClampPreservesBitonic(s, t);
        ClampIs01(s, t);
        merge01Sorts(clamp(s, t));
    }
    SortedViaClamp(bitonicMerge(s));
}

// ===== Recursive bitonic sort =====

function reverse(s: seq<int>): seq<int>
    ensures |reverse(s)| == |s|
    ensures multiset(reverse(s)) == multiset(s)
{
    if s == [] then []
    else
        assert s == s[0..|s|-1] + [s[|s|-1]];
        [s[|s| - 1]] + reverse(s[0..|s| - 1])
}

lemma ReverseIndex(s: seq<int>)
    ensures forall k :: 0 <= k < |s| ==> reverse(s)[k] == s[|s| - 1 - k]
{
    if s == [] {
    } else {
        ReverseIndex(s[0..|s|-1]);
    }
}

lemma ReverseFlips(s: seq<int>)
    requires sortedAsc(s)
    ensures sortedDesc(reverse(s))
{
    ReverseIndex(s);
    forall i, j | 0 <= i < j < |reverse(s)|
        ensures reverse(s)[i] >= reverse(s)[j]
    {
        assert reverse(s)[i] == s[|s| - 1 - i];
        assert reverse(s)[j] == s[|s| - 1 - j];
    }
}

// An ascending run followed by a descending run is bitonic (unimodal, r = 0).
lemma BuildBitonic(left: seq<int>, right: seq<int>)
    requires sortedAsc(left) && sortedDesc(right)
    ensures bitonic(left + right)
{
    var s := left + right;
    var p := |left|;
    assert s[..p] == left;
    assert s[p..] == right;
    assert unimodal(s);
    assert rotate(s, 0) == s;
    assert bitonic(s);
}

function bitonicSort(s: seq<int>): seq<int>
    requires |s| == 0 || IsPowerOfTwo(|s|)
    ensures |bitonicSort(s)| == |s|
    ensures multiset(bitonicSort(s)) == multiset(s)
    ensures sortedAsc(bitonicSort(s))
    decreases |s|
{
    if |s| <= 1 then s
    else
        var n := |s| / 2;
        HalfIsPowerOfTwo(|s|);
        var left  := bitonicSort(s[..n]);
        var right := reverse(bitonicSort(reverse(s[n..])));
        ReverseFlips(bitonicSort(reverse(s[n..])));
        BuildBitonic(left, right);
        assert s == s[..n] + s[n..];
        mergeSorts(left + right);
        bitonicMerge(left + right)
}

}
