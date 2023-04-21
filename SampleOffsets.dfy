// Implementation of csr_sample_offsets (scipy/sparse/sparsetools/csr.h, line 1559).
// Given a CSR matrix and two arrays representing (row, col) indices,
// returns the corresponding index of those coordinates in the matrix; or -1 if the index does not exist.

include "csr.dfy"

// Our target postcondition: if entry exists at row Bi[n] and column Bj[n], then Bp[n] == the index of the entry
// Otherwise, Bp[n] == -1
predicate SampleOffsetsTarget(matrix: CSRMatrix, Bi: seq<int>, Bj: seq<int>, Bp: seq<int>)
    reads matrix
    requires matrix.Valid()
    requires |Bi| == |Bj| == |Bp|
    requires forall n :: 0 <= n < |Bi| ==> -matrix.nrows <= Bi[n] < matrix.nrows
{
    (forall n :: 0 <= n < |Bp| ==> 0 <= Bp[n] < |matrix.indices| || Bp[n] == -1) &&
    forall n :: 0 <= n < |Bp| ==>
        (if JExists(matrix.indices, matrix.indptr, positiveIndex(Bi[n], matrix.nrows), positiveIndex(Bj[n], matrix.ncols))
            then 0 <= Bp[n] < |matrix.indices|
                && getX(matrix.indices, matrix.indptr, Bp[n]) == positiveIndex(Bi[n], matrix.nrows)
                && getY(matrix.indices, matrix.indptr, Bp[n]) == positiveIndex(Bj[n], matrix.ncols)
            else Bp[n] == -1)
}

function positiveIndex(i: int, n: int) : int
{
    if i < 0 then i + n else i
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
    var n := 0;
    while n < |Bi|
        invariant 0 <= n <= |Bi|
        invariant |Bp| == n
        invariant SampleOffsetsTarget(matrix, Bi[..n], Bj[..n], Bp)
    {
        var i := if Bi[n] < 0 then Bi[n] + matrix.nrows else Bi[n];
        var j := if Bj[n] < 0 then Bj[n] + matrix.ncols else Bj[n];

        var row_start := matrix.indptr[i];
        var row_end   := matrix.indptr[i+1];
        var offset := -1;

        // This represents the branch at lines 1598-1621 of the source code.
        // An alternative algorithm is used when the matrix meets certain heuristics.
        // TODO Verify this alternative algorithm in a separate function.
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
                // since we assert our input matrix is canonical
            }
            jj := jj + 1;
            if offset >= 0
            {
                JBoundsDetermineX(matrix.indices, matrix.indptr, offset, i);
            }
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
