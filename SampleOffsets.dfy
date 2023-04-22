// Implementation of csr_sample_offsets (scipy/sparse/sparsetools/csr.h, line 1559).
// Given a CSR matrix and two arrays representing (row, col) indices,
// returns the corresponding index of those coordinates in the matrix; or -1 if the index does not exist.

include "csr.dfy"

predicate IsRealIndex(matrix: CSRMatrix, j: int)
    reads matrix
{
    0 <= j < |matrix.indices|
}

// Our target postcondition: if entry exists at row Bi[n] and column Bj[n], then Bp[n] == the index of the entry
// Otherwise, Bp[n] == -1
predicate SampleOffsetsTarget(matrix: CSRMatrix, Bi: seq<int>, Bj: seq<int>, Bp: seq<int>)
    reads matrix
    requires matrix.Valid()
    requires |Bi| == |Bj| == |Bp|
    requires forall n :: 0 <= n < |Bi| ==> -matrix.nrows <= Bi[n] < matrix.nrows
{
    (forall n :: 0 <= n < |Bp| ==> IsRealIndex(matrix, Bp[n]) || Bp[n] == -1) &&
    forall n :: 0 <= n < |Bp| ==>
        (if JExists(matrix.indices, matrix.indptr, positiveIndex(Bi[n], matrix.nrows), positiveIndex(Bj[n], matrix.ncols))
            then IsRealIndex(matrix, Bp[n])
                && getX(matrix.indices, matrix.indptr, Bp[n]) == positiveIndex(Bi[n], matrix.nrows)
                && getY(matrix.indices, matrix.indptr, Bp[n]) == positiveIndex(Bj[n], matrix.ncols)
            else Bp[n] == -1)
}

function positiveIndex(i: int, n: int) : int
{
    if i < 0 then i + n else i
}

// https://en.cppreference.com/w/cpp/algorithm/lower_bound
// Returns the index of the first element in the range [first, last) 
// that does not satisfy element < value, (i.e. greater or equal to), 
// or last if no such element is found. 
// All input elements for which element < value must precede all elements for which element >= value.
method StdLowerBound(s: seq<int>, first: int, last: int, value: int) returns (index: int)
    requires 0 <= first <= last <= |s|
    requires forall i, j :: first <= i < j < last ==> (s[j] < value ==> s[i] < value)

    ensures first <= index <= last
    ensures forall i :: first <= i < index ==> s[i] < value
    ensures index == last || (forall i :: index <= i < last ==> s[i] >= value)
{
    // We give an iterative implementation here, but it is possible to implement this using binary search
    // (in fact, the reference implementation in the linked documentation does exactly this)
    index := first;
    while index < last && s[index] < value
        invariant first <= index <= last
        invariant forall i :: first <= i < index ==> i <= last-1 && s[i] < value
    {
        index := index + 1;
    }
    if index < last
    {
        assert s[index] >= value;
        assert forall i :: index < i < last ==> s[i] >= value;
    }
}

method SampleOffsets(matrix: CSRMatrix, Bi: seq<int>, Bj: seq<int>) returns (Bp: seq<int>)
    requires matrix.Valid()
    requires |Bi| == |Bj|
    requires forall n :: 0 <= n < |Bi| ==> -matrix.nrows <= Bi[n] < matrix.nrows

    ensures matrix.Valid()
    ensures |Bp| == |Bi|
    ensures SampleOffsetsTarget(matrix, Bi, Bj, Bp)
{
    Bp := [];

    // constant is arbitrary
    var threshold := |matrix.indices| / 10;

    if (|Bi| > threshold && Canonical(matrix.indices, matrix.indptr))
    {
        var n := 0;
        while n < |Bi|
            invariant 0 <= n <= |Bi|
            invariant |Bp| == n
            invariant SampleOffsetsTarget(matrix, Bi[..n], Bj[..n], Bp)
        {
            // Algorithm using std::lower_bound, lines 1573-1593
            var i := if Bi[n] < 0 then Bi[n] + matrix.nrows else Bi[n];
            var j := if Bj[n] < 0 then Bj[n] + matrix.ncols else Bj[n];

            var row_start := matrix.indptr[i];
            var row_end   := matrix.indptr[i+1];

            if row_start < row_end
            {
                var offset := StdLowerBound(matrix.indices, row_start, row_end, j);

                if offset < row_end && matrix.indices[offset] == j
                {
                    Bp := Bp + [offset];
                    JBoundsDetermineX(matrix.indices, matrix.indptr, offset, i);
                }
                else
                {
                    if offset == row_end
                    {
                        assert forall k :: row_start <= k < row_end ==> matrix.indices[k] < j;
                    } 
                    else 
                    {
                        assert matrix.indices[offset] > j;
                        assert forall k :: row_start <= k < offset ==> matrix.indices[k] < j;
                        assert forall k :: offset < k < row_end ==> matrix.indices[k] > matrix.indices[offset] > j;
                    }
                    assert j !in matrix.indices[row_start..row_end];
                    Bp := Bp + [-1];
                }
            }
            else
            {
                Bp := Bp + [-1];
            }
            assert Bp[n] == -1 ==> j !in matrix.indices[row_start..row_end];
            n := n + 1;
        }
    } else {
        var n := 0;
        while n < |Bi|
            invariant 0 <= n <= |Bi|
            invariant |Bp| == n
            invariant SampleOffsetsTarget(matrix, Bi[..n], Bj[..n], Bp)
        {
            // Linear search algorithm, lines 1598-1621
            var i := if Bi[n] < 0 then Bi[n] + matrix.nrows else Bi[n];
            var j := if Bj[n] < 0 then Bj[n] + matrix.ncols else Bj[n];

            var row_start := matrix.indptr[i];
            var row_end   := matrix.indptr[i+1];

            var offset := -1;

            var jj := row_start;
            while(jj < row_end)
                invariant row_start <= jj <= row_end
                invariant offset == -1 || row_start <= offset < jj
                invariant offset >= 0 ==> getX(matrix.indices, matrix.indptr, offset) == i && getY(matrix.indices, matrix.indptr, offset) == j
                invariant offset == -1 ==> j !in matrix.indices[row_start..jj]
            {
                if (matrix.indices[jj] == j)
                {
                    offset := jj;
                    // The source code further checks for duplicates here; this is unnecessary in our case
                    // since we assert our input matrix is unique
                    JBoundsDetermineX(matrix.indices, matrix.indptr, offset, i);
                }
                jj := jj + 1;
            }

            // These assertions, along with their contrapositives and the above loop invariants, prove our target postcondition.
            JExistenceConditionForGivenX(matrix.indices, matrix.indptr, matrix.ncols, i);
            if offset >= 0
            {
                JUniqueInCanonicalMatrix(matrix.indices, matrix.indptr, i, j, offset);
                assert JExists(matrix.indices, matrix.indptr, i, j);
                assert j in matrix.indices[row_start..jj];
            }
            assert offset == -1 ==> j !in matrix.indices[row_start..jj];
            Bp := Bp + [offset];
            n := n + 1;
        }
    }
}
