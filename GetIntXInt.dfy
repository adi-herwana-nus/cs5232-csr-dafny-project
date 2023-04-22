// Implementation of _get_intXint (scipy/sparse/_compressed.py, line 654),
// which directly calls get_csr_submatrix (verified in GetSubmatrix.dfy)
// This is the method called when the Python code uses M[x, y] to get the value at row x, column y.

include "csr.dfy"
include "GetSubmatrix.dfy"

// A somewhat specific application of the principle, but it is sufficient to prove the following lemma.
lemma PigeonholePrinciple(arr: seq<int>, arrmin: int, arrmax: int)
    requires 1 <= arrmax - arrmin < |arr|
    requires forall i :: 0 <= i < |arr| ==> arrmin <= arr[i] < arrmax
    ensures exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j]
    decreases arrmax - arrmin
{
    if arrmax - arrmin == 1
    {
        assert |arr| >= 2;
        assert arr[0] == arr[1];
    }
    else 
    {
        // Split sequence into values that equal arrmax-1, and those that don't equal arrmax-1.
        // Also store the indices where those values came from for easier reasoning.
        var s1: seq<int>, s2: seq<int> := [], [];
        var i1: seq<int>, i2: seq<int> := [], [];
        var i := 0;
        while i < |arr|
            invariant 0 <= i <= |arr|
            invariant |i1| == |s1|
            invariant |i2| == |s2|
            invariant |i1| + |i2| == i
            invariant forall j :: 0 <= j < |i1| ==> 0 <= i1[j] < i
            invariant forall j :: 0 <= j < |i2| ==> 0 <= i2[j] < i
            invariant forall j,k :: 0 <= j < k < |i1| ==> i1[j] < i1[k]
            invariant forall j,k :: 0 <= j < k < |i2| ==> i2[j] < i2[k]
            invariant forall j :: 0 <= j < |i1| ==> (arr[i1[j]] == s1[j] == arrmax-1)
            invariant forall j :: 0 <= j < |i2| ==> (arr[i2[j]] == s2[j] < arrmax-1)
        {
            if arr[i] == arrmax-1
            {
                s1 := s1 + [arr[i]];
                i1 := i1 + [i];
            }
            else
            {
                s2 := s2 + [arr[i]];
                i2 := i2 + [i];
            }
            i := i + 1;
        }

        if |i1| >= 2
        {
            assert arr[i1[0]] == arr[i1[1]];
        }
        else 
        {
            PigeonholePrinciple(s2, arrmin, arrmax-1);
        }
    }
}

lemma CanonicalIndicesLimited(indices: seq<int>, indptr: seq<int>, ncols: int)
    requires ValidCSRIndex(indices, indptr)
    requires Unique(indices, indptr)
    requires forall j :: 0 <= j < |indices| ==> indices[j] < ncols
    requires 0 <= ncols
    decreases |indptr|

    ensures |indices| <= (|indptr| - 1) * ncols
{
    if |indptr| == 1 
    {
        assert |indptr| - 1 == 0;
    }
    else if |indptr| == 2
    {
        if |indices| > ncols
        {
            if ncols > 0 
            {
                assert 1 <= ncols < |indices|;
                assert forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < ncols;
                PigeonholePrinciple(indices, 0, ncols);
                assert exists i,j :: indptr[0] <= i < j < indptr[1] && indices[i] == indices[j]; // Violates Unique precondition
            } 
            else 
            {
                assert |indices| >= 1;
                assert indices[0] >= 0;
                assert indices[0] < 0;
            }
        }
    }
    else
    {
        // all rows but the last
        var head_indices := indices[..indptr[|indptr|-2]];
        var head_indptr := indptr[..|indptr|-1];
        // last row
        var tail_indices := indices[indptr[|indptr|-2]..indptr[|indptr|-1]];
        var tail_indptr := [0, indptr[|indptr|-1] - indptr[|indptr|-2]];

        CanonicalIndicesLimited(head_indices, head_indptr, ncols);
        CanonicalIndicesLimited(tail_indices, tail_indptr, ncols);
    }
}

method GetIntXInt(matrix: CSRMatrix, row: int, col: int) returns (value: int)
    requires 0 <= row < matrix.nrows
    requires 0 <= col < matrix.ncols
    requires matrix.Valid()

    ensures matrix.Valid()
    ensures JExists(matrix.indices, matrix.indptr, row, col) ==> DataAt(matrix.data, matrix.indices, matrix.indptr, row, col) == {value}
    ensures !JExists(matrix.indices, matrix.indptr, row, col) ==> value == 0
{
    var value_matrix := GetSubmatrix(matrix, row, row+1, col, col+1);

    // The source code reduces the submatrix to a singular value by calling np.sum on the data array,
    // however we can show that the resulting data array always has either 0 or 1 elements, and thus the assignment below is equivalent.
    assert JExists(matrix.indices, matrix.indptr, row, col) <==> JExists(value_matrix.indices, value_matrix.indptr, 0, 0);
    CanonicalIndicesLimited(value_matrix.indices, value_matrix.indptr, 1);
    value := if |value_matrix.data| == 0 then 0 else value_matrix.data[0];
    
    if value != 0
    {
        assert value_matrix.indices[0] == 0;
        assert 0 in value_matrix.indices[value_matrix.indptr[0]..value_matrix.indptr[1]];
        JExistenceCondition(value_matrix.indices, value_matrix.indptr, 1);
        // This is the contrapositive of the second postcondition, which proves its validity
        assert JExists(value_matrix.indices, value_matrix.indptr, 0, 0);
    }
}
