// Insertion sort — the `isort` function and the lemmas it needs, extracted from
// Algorithms/insertionSort.dfy. Used by the bitonic-sort case study as an
// independent reference sort (for differential testing) and to build bitonic
// inputs (sort, then rotate).
module InsertionSort {

    predicate sortedRec(list: seq<int>) {
        if list == [] then true
        else (forall y :: y in list[1..] ==> list[0] <= y) && sortedRec(list[1..])
    }

    function insort(a: int, list: seq<int>): seq<int>
        requires sortedRec(list)
        ensures a in insort(a, list)
        ensures forall x :: x in list ==> x in insort(a, list)
    {
        if list == [] then [a]
        else if a <= list[0] then [a] + list
        else [list[0]] + insort(a, list[1..])
    }

    lemma insortPreservesMultiset(a: int, list: seq<int>)
        requires sortedRec(list)
        ensures multiset(insort(a, list)) == multiset{a} + multiset(list)
    {
        if list == [] {
        } else if a <= list[0] {
        } else {
            assert list == [list[0]] + list[1..];
            assert multiset(insort(a, list)) == multiset{a} + multiset(list);
        }
    }

    lemma insortPreservesSorted(a: int, list: seq<int>)
        requires sortedRec(list)
        ensures sortedRec(insort(a, list))
    {
        if list == [] {
        } else if a <= list[0] {
            assert list == [list[0]] + list[1..];
            assert insort(a, list) == [a] + list;
        } else {
            insortPreservesMultiset(a, list[1..]);
            assert forall x :: x in insort(a, list[1..]) ==>
                x in multiset(insort(a, list[1..])) ==> x in multiset(list[1..]) || x in multiset{a};
            assert forall x :: x in insort(a, list[1..]) ==> x in list[1..] || x in {a};
        }
    }

    lemma insortProperties(a: int, list: seq<int>)
        requires sortedRec(list)
        ensures multiset(insort(a, list)) == multiset{a} + multiset(list)
        ensures sortedRec(insort(a, list))
    {
        insortPreservesMultiset(a, list);
        insortPreservesSorted(a, list);
    }

    // The sorting function: a sorted permutation of `list`.
    function isort(list: seq<int>): seq<int>
        ensures multiset(list) == multiset(isort(list))
        ensures sortedRec(isort(list))
        ensures forall x :: x in list ==> x in isort(list)
    {
        if list == [] then []
        else
            var rest := isort(list[1..]);
            assert list == [list[0]] + list[1..];
            insortProperties(list[0], rest);
            insort(list[0], rest)
    }
}
