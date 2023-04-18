include "matrix.dfy"

predicate ValidCSRIndex(indices: seq<int>, indptr: seq<int>) 
{
    |indptr| >= 1 &&
    indptr[0] == 0 &&
    indptr[|indptr| - 1] == |indices| &&
    (forall i :: 0 <= i < |indices| ==> 0 <= indices[i]) &&
    (forall i :: 0 <= i < |indptr| - 1 ==> 0 <= indptr[i] <= |indices|) &&
    (forall i, j :: 0 <= i < j < |indptr| ==> indptr[i] <= indptr[j])
}

predicate Canonical(indices: seq<int>, indptr: seq<int>)
    requires ValidCSRIndex(indices, indptr)
{
    forall row :: 0 <= row < |indptr|-1 ==> forall i,j :: indptr[row] <= i < j < indptr[row+1] ==> indices[i] < indices[j]
}

function getX(indices: seq<int>, indptr: seq<int>, j: int) : int
    requires ValidCSRIndex(indices, indptr)
    requires 0 <= j < |indices|
    decreases |indptr|
{
    if |indptr| == 2 then 0 else (
        if j >= indptr[|indptr| - 2] then |indptr| - 2
        else getX(indices[..indptr[|indptr|-2]], indptr[..|indptr|-1], j)
    )
}

lemma XIsUniqueAndInBounds(indices: seq<int>, indptr: seq<int>, j: int, x: int)
    requires ValidCSRIndex(indices, indptr)
    requires 0 <= j < |indices|
    requires x == getX(indices, indptr, j)
    decreases |indptr|

    ensures 0 <= x <= |indptr| - 2
    ensures indptr[x] <= j < indptr[x+1]
    ensures forall x1 :: 0 <= x1 < x ==> j >= indptr[x1+1]
    ensures forall x1 :: x < x1 <= |indptr|-2 ==> j < indptr[x1]
    ensures forall x1 :: 0 <= x1 <= |indptr| - 2 ==> ((indptr[x1] <= j < indptr[x1+1]) <==> (x1 == x))
{
    if |indptr| == 2
    {
        assert x == 0;
        assert 0 <= x <= |indptr| - 2;
        assert indptr[x] == 0 <= j;
        assert indptr[x+1] == indptr[|indptr| - 1] == |indices| > j;
    }
    else
    {
        if j >= indptr[|indptr| - 2]
        {
            assert x == |indptr| - 2;
            assert 0 <= x <= |indptr| - 2;
            assert indptr[x+1] == indptr[|indptr| - 1] == |indices| > j;
        }
        else
        {
            var head_indices, head_indptr := indices[..indptr[|indptr|-2]], indptr[..|indptr|-1];
            var head_x := getX(head_indices, head_indptr, j);
            assert x == head_x;
            XIsUniqueAndInBounds(head_indices, head_indptr, j, head_x);
        }
    }
}

lemma JBoundsDetermineX(indices: seq<int>, indptr: seq<int>, j: int, x: int)
    requires ValidCSRIndex(indices, indptr)
    requires 0 <= j < |indices|
    requires 0 <= x <= |indptr| - 2
    requires indptr[x] <= j < indptr[x+1]
    decreases |indptr|
    ensures getX(indices, indptr, j) == x
{
    if |indptr| == 2
    {
        assert x == 0;
        assert 0 <= x <= |indptr| - 2;
        assert indptr[x] == 0 <= j;
        assert indptr[x+1] == indptr[|indptr| - 1] == |indices| > j;
    }
    else
    {
        if j >= indptr[|indptr| - 2]
        {
            assert x == |indptr| - 2;
            assert 0 <= x <= |indptr| - 2;
            assert indptr[x+1] == indptr[|indptr| - 1] == |indices| > j;
        }
        else
        {
            var head_indices, head_indptr := indices[..indptr[|indptr|-2]], indptr[..|indptr|-1];
            var head_x := getX(head_indices, head_indptr, j);
            JBoundsDetermineX(head_indices, head_indptr, j, head_x);
            assert x == head_x;
        }
    }
}

function getY(indices: seq<int>, indptr: seq<int>, j: int) : int
    requires ValidCSRIndex(indices, indptr)
    requires 0 <= j < |indices|
{
    indices[j]
}

function getJs(indices: seq<int>, indptr: seq<int>, x: int, y: int) : set<int>
    requires ValidCSRIndex(indices, indptr)
    requires Canonical(indices, indptr)
{
    set j | 0 <= j < |indices| && getX(indices, indptr, j) == x && getY(indices, indptr, j) == y
}

predicate JExists(indices: seq<int>, indptr: seq<int>, x: int, y: int)
    requires ValidCSRIndex(indices, indptr)
    requires Canonical(indices, indptr)
{
    |getJs(indices, indptr, x, y)| == 1
}

function DataAt(data: seq<int>, indices: seq<int>, indptr: seq<int>, x: int, y: int): set<int>
    requires |data| == |indices|
    requires ValidCSRIndex(indices, indptr)
    requires Canonical(indices, indptr)
{
    set j | j in getJs(indices, indptr, x, y) :: data[j]
}

lemma XYUniqueInCanonicalMatrix(indices: seq<int>, indptr: seq<int>, j1: int, j2: int)
    requires ValidCSRIndex(indices, indptr)
    requires Canonical(indices, indptr)
    requires 0 <= j1 < |indices|
    requires 0 <= j2 < |indices|
    requires getX(indices, indptr, j1) == getX(indices, indptr, j2)
    requires getY(indices, indptr, j1) == getY(indices, indptr, j2)
    ensures j1 == j2
{
    if j1 != j2
    {
        var x := getX(indices, indptr, j1);
        XIsUniqueAndInBounds(indices, indptr, j1, x);
        XIsUniqueAndInBounds(indices, indptr, j2, x);

        // Proof by contradiction (Dafny verifies even without this, but it is included for completeness)
        assert indptr[x] <= j1 < indptr[x+1];
        assert indptr[x] <= j2 < indptr[x+1];
        if j1 < j2
        {
            assert indptr[x] <= j1 < j2 < indptr[x+1] ==> indices[j1] < indices[j2];
        }
        else
        {
            assert indptr[x] <= j2 < j1 < indptr[x+1] ==> indices[j2] < indices[j1];
        }
        assert getY(indices, indptr, j1) == indices[j1] != indices[j2] == getY(indices, indptr, j2);
        assert false;
    }
}

lemma JUniqueInCanonicalMatrix(indices: seq<int>, indptr: seq<int>, x: int, y: int, j: int)
    requires ValidCSRIndex(indices, indptr)
    requires Canonical(indices, indptr)
    requires 0 <= j < |indices|
    requires getX(indices, indptr, j) == x
    requires getY(indices, indptr, j) == y

    ensures getJs(indices, indptr, x, y) == {j}
{
    var jset := getJs(indices, indptr, x, y);
    if jset != {j}
    {
        assert exists j2 :: j2 in jset && j2 != j;
        forall j2 | j2 in jset && j2 != j
            ensures false
        {
            XYUniqueInCanonicalMatrix(indices, indptr, j, j2);
        }
    }
}

lemma DataUniqueInCanonicalMatrix(data: seq<int>, indices: seq<int>, indptr: seq<int>, x: int, y: int, j: int)
    requires ValidCSRIndex(indices, indptr)
    requires Canonical(indices, indptr)
    requires 0 <= j < |indices|
    requires |data| == |indices|
    requires getX(indices, indptr, j) == x
    requires getY(indices, indptr, j) == y

    ensures DataAt(data, indices, indptr, x, y) == {data[j]}
{
    JUniqueInCanonicalMatrix(indices, indptr, x, y, j);
}

lemma JExistenceConditionForGivenXY(indices: seq<int>, indptr: seq<int>, ncols: int, x: int, y: int)
    requires ValidCSRIndex(indices, indptr)
    requires Canonical(indices, indptr)
    requires 0 <= x < |indptr| - 1
    ensures JExists(indices, indptr, x, y) <==> y in indices[indptr[x]..indptr[x+1]];
{
    if y in indices[indptr[x]..indptr[x+1]]
    {
        forall j | indptr[x] <= j < indptr[x+1] && indices[j] == y
            ensures JExists(indices, indptr, x, y)
        {
            JBoundsDetermineX(indices, indptr, j, x);
            assert getX(indices, indptr, j) == x;
            JUniqueInCanonicalMatrix(indices, indptr, x, y, j);
        } 
    }
    if JExists(indices, indptr, x, y)
    {
        forall j | j in getJs(indices, indptr, x, y)
            ensures y in indices[indptr[x]..indptr[x+1]]
        {
            assert getX(indices, indptr, j) == x;
            XIsUniqueAndInBounds(indices, indptr, j, x);
            assert y in indices[indptr[x]..indptr[x+1]];
        }
    }
}

lemma JExistenceConditionForGivenX(indices: seq<int>, indptr: seq<int>, ncols: int, x: int)
    requires ValidCSRIndex(indices, indptr)
    requires Canonical(indices, indptr)
    requires 0 <= x < |indptr| - 1
    ensures forall y :: 0 <= y < ncols ==>
        (JExists(indices, indptr, x, y) <==> y in indices[indptr[x]..indptr[x+1]])
{
    forall y | 0 <= y < ncols 
        ensures (JExists(indices, indptr, x, y) <==> y in indices[indptr[x]..indptr[x+1]])
    {
        if y in indices[indptr[x]..indptr[x+1]]
        {
            forall j | indptr[x] <= j < indptr[x+1] && indices[j] == y
                ensures JExists(indices, indptr, x, y)
            {
                JBoundsDetermineX(indices, indptr, j, x);
                assert getX(indices, indptr, j) == x;
                JUniqueInCanonicalMatrix(indices, indptr, x, y, j);
            } 
        }
        if JExists(indices, indptr, x, y)
        {
            forall j | j in getJs(indices, indptr, x, y)
                ensures y in indices[indptr[x]..indptr[x+1]]
            {
                assert getX(indices, indptr, j) == x;
                XIsUniqueAndInBounds(indices, indptr, j, x);
                assert y in indices[indptr[x]..indptr[x+1]];
            }
        }
    }
}

lemma JExistenceCondition(indices: seq<int>, indptr: seq<int>, ncols: int)
    requires ValidCSRIndex(indices, indptr)
    requires Canonical(indices, indptr)
    ensures forall x :: 0 <= x < |indptr| - 1 ==> 
        forall y :: 0 <= y < ncols ==>
            (JExists(indices, indptr, x, y) <==> y in indices[indptr[x]..indptr[x+1]])
{
    forall x | 0 <= x < |indptr| - 1 
        ensures forall y :: 0 <= y < ncols ==> (JExists(indices, indptr, x, y) <==> y in indices[indptr[x]..indptr[x+1]])
    {
        JExistenceConditionForGivenX(indices, indptr, ncols, x);
    }
}

// Check if (indices1, indptr1) describes a partial CSR matrix of (indices2, indptr2) obtained
// by removing zero or more of the latter's final row(s).
predicate IsHeadMatrix(indices1: seq<int>, indptr1: seq<int>, indices2: seq<int>, indptr2: seq<int>)
    requires ValidCSRIndex(indices1, indptr1)
    requires ValidCSRIndex(indices2, indptr2)
{
    |indptr1| <= |indptr2| &&
    (forall i :: 0 <= i < |indptr1| ==> indptr1[i] == indptr2[i]) &&
    (forall j :: 0 <= j < |indices1| ==> indices1[j] == indices2[j])
}

predicate IsHeadMatrixWithData (data1: seq<int>, indices1: seq<int>, indptr1: seq<int>, data2: seq<int>, indices2: seq<int>, indptr2: seq<int>)
    requires ValidCSRIndex(indices1, indptr1)
    requires |data1| == |indices1|
    requires ValidCSRIndex(indices2, indptr2)
    requires |data2| == |indices2|
{
    IsHeadMatrix(indices1, indptr1, indices2, indptr2) &&
    (forall j :: 0 <= j < |data1| ==> data1[j] == data2[j])
}

lemma AddingRowsPreservesExistingPositions(indices1: seq<int>, indptr1: seq<int>, indices2: seq<int>, indptr2: seq<int>)
    requires ValidCSRIndex(indices1, indptr1)
    requires ValidCSRIndex(indices2, indptr2)
    requires IsHeadMatrix(indices1, indptr1, indices2, indptr2)

    ensures forall j :: 0 <= j < |indices1| ==> getX(indices1, indptr1, j) == getX(indices2, indptr2, j)
    ensures forall j :: 0 <= j < |indices1| ==> getY(indices1, indptr1, j) == getY(indices2, indptr2, j)
{
    forall j | 0 <= j < |indices1|
        ensures getX(indices1, indptr1, j) == getX(indices2, indptr2, j)
    {
        var x1, x2 := getX(indices1, indptr1, j), getX(indices2, indptr2, j);
        XIsUniqueAndInBounds(indices1, indptr1, j, x1);
        XIsUniqueAndInBounds(indices2, indptr2, j, x2);
        assert 0 <= x2 <= |indptr1| - 2;
        assert x1 == x2;
    }
}

lemma AddingRowsPreservesJExists(indices1: seq<int>, indptr1: seq<int>, indices2: seq<int>, indptr2: seq<int>, ncols: int)
    requires ValidCSRIndex(indices1, indptr1)
    requires Canonical(indices1, indptr1)
    requires ValidCSRIndex(indices2, indptr2)
    requires Canonical(indices2, indptr2)
    requires IsHeadMatrix(indices1, indptr1, indices2, indptr2)

    ensures forall x :: 0 <= x < |indptr1| - 1 ==> (
        forall y :: 0 <= y < ncols ==> (
            JExists(indices1, indptr1, x, y) <==> JExists(indices2, indptr2, x, y)
        )
    )
{
    forall x | 0 <= x < |indptr1| - 1 
        ensures forall y :: 0 <= y < ncols ==> (
            JExists(indices1, indptr1, x, y) <==> JExists(indices2, indptr2, x, y)
        )
    {
        forall y | 0 <= y < ncols 
            ensures JExists(indices1, indptr1, x, y) <==> JExists(indices2, indptr2, x, y)
        {
            JExistenceConditionForGivenXY(indices1, indptr1, ncols, x, y);
            JExistenceConditionForGivenXY(indices2, indptr2, ncols, x, y);
        }
    }
}
lemma AddingRowsPreservesExistingData(data1: seq<int>, indices1: seq<int>, indptr1: seq<int>, data2: seq<int>, indices2: seq<int>, indptr2: seq<int>, ncols: int)
    requires ValidCSRIndex(indices1, indptr1)
    requires Canonical(indices1, indptr1)
    requires |data1| == |indices1|
    requires ValidCSRIndex(indices2, indptr2)
    requires Canonical(indices2, indptr2)
    requires |data2| == |indices2|
    requires IsHeadMatrixWithData(data1, indices1, indptr1, data2, indices2, indptr2)

    ensures forall x :: 0 <= x < |indptr1| - 1 ==> (
        forall y :: 0 <= y < ncols ==> (
            (JExists(indices1, indptr1, x, y) ==>
                DataAt(data1, indices1, indptr1, x, y) == DataAt(data2, indices2, indptr2, x, y))
        )
    )
{
    AddingRowsPreservesJExists(indices1, indptr1, indices2, indptr2, ncols);
    forall x | 0 <= x < |indptr1| - 1 
        ensures forall y :: 0 <= y < ncols ==> (
            (JExists(indices1, indptr1, x, y) ==>
                DataAt(data1, indices1, indptr1, x, y) == DataAt(data2, indices2, indptr2, x, y))
        )
    {
        forall y | 0 <= y < ncols 
            ensures (JExists(indices1, indptr1, x, y) ==>
                DataAt(data1, indices1, indptr1, x, y) == DataAt(data2, indices2, indptr2, x, y))
        {
            if JExists(indices1, indptr1, x, y) 
            {
                forall j | j in getJs(indices1, indptr1, x, y)
                    ensures DataAt(data1, indices1, indptr1, x, y) == DataAt(data2, indices2, indptr2, x, y)
                {
                    AddingRowsPreservesExistingPositions(indices1, indptr1, indices2, indptr2);
                    DataUniqueInCanonicalMatrix(data1, indices1, indptr1, x, y, j);
                    assert DataAt(data1, indices1, indptr1, x, y) == {data1[j]};
                    assert getX(indices2, indptr2, j) == x;
                    assert getY(indices2, indptr2, j) == y;
                    JUniqueInCanonicalMatrix(indices2, indptr2, x, y, j);
                    assert DataAt(data2, indices2, indptr2, x, y) == {data2[j]};
                }
            }
        }
    }
}

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
    requires Canonical(indices, indptr)
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
                assert exists i,j :: indptr[0] <= i < j < indptr[1] && indices[i] == indices[j]; // Violates Canonical precondition
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

class CSRMatrix {
    var data: seq<int>
    var indices: seq<int>
    var indptr: seq<int>
    var nrows: int
    var ncols: int

    constructor (data: seq<int>, indices: seq<int>, indptr: seq<int>, nrows: int, ncols: int) 
        requires |data| == |indices|
        requires ValidCSRIndex(indices, indptr)
        requires Canonical(indices, indptr)
        requires |indptr| == nrows + 1
        requires 0 <= ncols
        requires forall j :: 0 <= j < |indices| ==> indices[j] < ncols
        
        ensures this.data == data
        ensures this.indices == indices
        ensures this.indptr == indptr
        ensures this.nrows == nrows
        ensures this.ncols == ncols
        ensures Valid()
    {
        this.data := data;
        this.indices := indices;
        this.indptr := indptr;
        this.nrows := nrows;
        this.ncols := ncols;
        JExistenceCondition(indices, indptr, ncols);
    }

    predicate Valid() 
        reads this
    {
        |data| == |indices| &&
        ValidCSRIndex(this.indices, this.indptr) &&
        Canonical(this.indices, this.indptr) &&
        RowColValid() &&
        forall x :: 0 <= x < |indptr| - 1 ==> 
            forall y :: 0 <= y < ncols ==>
                (JExists(indices, indptr, x, y) <==> y in indices[indptr[x]..indptr[x+1]])
    }

    predicate RowColValid()
        reads this
    {
        |indptr| == nrows + 1 && 0 <= ncols && forall j :: 0 <= j < |indices| ==> indices[j] < ncols
    }

    // Implementation of get_csr_submatrix (scipy/sparse/csr.h, line 1181)
    // The typical numpy-style getter M[x, y] is implemented as a special case of this method
    // (where ir0 = x, ir1 = x+1, ic0 = y, ic1 = y+1).
    // This implies SciPy uses an O(nnz) search algorithm to access matrix entries,
    // even though an O(log(nnz)) algorithm should be possible using binary search.
    method GetSubmatrix(ir0: int, ir1: int, ic0: int, ic1: int) returns (new_matrix: CSRMatrix)
        requires 0 <= ir0 < ir1 <= nrows
        requires ir0 < nrows
        requires 0 <= ic0 < ic1 <= ncols
        requires ic0 < ncols
        requires Valid()

        ensures new_matrix.nrows == ir1 - ir0
        ensures new_matrix.ncols == ic1 - ic0
        ensures new_matrix.Valid()

        // Our primary goal: for all valid x,y coordinates in the new matrix we prove the following:
        ensures forall x :: 0 <= x < new_matrix.nrows ==> forall y :: 0 <= y <new_matrix.ncols ==> (
            // 1. The new matrix stores a value for (x, y) if and only if the old matrix stores a value for (x+ir0, y+ic0);
            (JExists(new_matrix.indices, new_matrix.indptr, x, y) <==> JExists(this.indices, this.indptr, x+ir0, y+ic0)) &&
            // 2. If the new matrix stores a value for (x, y), then it is equal to the value of the old matrix at (x+ir0, y+ic0).
            (JExists(new_matrix.indices, new_matrix.indptr, x, y) ==>
                DataAt(new_matrix.data, new_matrix.indices, new_matrix.indptr, x, y) == DataAt(this.data, this.indices, this.indptr, x+ir0, y+ic0))
        )
    {
        var new_n_row := ir1 - ir0;
        var new_n_col := ic1 - ic0;
        var kk := 0;
        // We skip the counting of nnz/allocation steps because our representation is not bound by CXX memory allocation rules

        // Assign.
        var new_data := [];
        var new_indices := [];
        var new_indptr := [0];
        var i := 0;

        while i < new_n_row
            invariant 0 <= i <= new_n_row

            invariant |new_indptr| == i+1
            invariant kk == |new_indices| == |new_data|

            invariant forall i1 :: 0 <= i1 < |new_indptr| ==> new_indptr[i1] <= kk
            invariant forall i1, j1 :: 0 <= i1 < j1 < |new_indptr| ==> new_indptr[i1] <= new_indptr[j1]
            invariant ValidCSRIndex(new_indices, new_indptr)

            invariant forall i1 :: 0 <= i1 < i-1 ==>
                forall j1, k1 :: new_indptr[i1] <= j1 < k1 < new_indptr[i1+1] ==> new_indices[j1] < new_indices[k1] 
            invariant Canonical(new_indices, new_indptr)

            invariant forall j1 :: 0 <= j1 < |new_indices| ==> 0 <= new_indices[j1] < new_n_col

            // Our goals
            invariant forall x :: 0 <= x < i ==> forall y :: 0 <= y < new_n_col ==> (
                (JExists(new_indices, new_indptr, x, y) <==> JExists(this.indices, this.indptr, x+ir0, y+ic0)) &&
                (JExists(new_indices, new_indptr, x, y) ==>
                    DataAt(new_data, new_indices, new_indptr, x, y) == DataAt(this.data, this.indices, this.indptr, x+ir0, y+ic0))
            )
        {
            ghost var prev_data, prev_indices, prev_indptr := new_data, new_indices, new_indptr;
            var row_start := this.indptr[ir0+i];
            var row_end   := this.indptr[ir0+i+1];

            forall jj | row_start <= jj < row_end
                ensures getX(this.indices, this.indptr, jj) == i+ir0
            {
                XIsUniqueAndInBounds(this.indices, this.indptr, jj, getX(this.indices, this.indptr, jj));
            }

            assert forall j1, k1 :: row_start <= j1 < k1 < row_end ==> this.indices[j1] < this.indices[k1];
            ghost var current_row_jjs: seq<int> := [];
            
            var jj := row_start;
            while jj < row_end
                invariant 0 <= row_start <= jj <= row_end <= |indices|

                invariant kk == |new_indices| == |new_data|

                invariant forall i1 :: 0 <= i1 < |new_indptr| ==> new_indptr[i1] <= kk
                invariant forall i1, j1 :: 0 <= i1 < j1 < |new_indptr| ==> new_indptr[i1] <= new_indptr[j1]
                invariant ValidCSRIndex(new_indices, new_indptr + [kk])

                invariant forall i1 :: 0 <= i1 < |new_indptr|-1 ==>
                    forall j1, k1 :: new_indptr[i1] <= j1 < k1 < new_indptr[i1+1] ==> new_indices[j1] < new_indices[k1] 

                invariant forall j1 :: 0 <= j1 < |new_indices| ==> 0 <= new_indices[j1] < new_n_col

                invariant |new_indices| == new_indptr[|new_indptr|-1] + |current_row_jjs|
                invariant forall j1 :: 0 <= j1 < |current_row_jjs| ==> row_start <= current_row_jjs[j1] < jj
                invariant forall j1 :: 0 <= j1 < |current_row_jjs| ==> new_indices[new_indptr[|new_indptr|-1] + j1] == this.indices[current_row_jjs[j1]] - ic0
                invariant forall j1, k1 :: 0 <= j1 < k1 < |current_row_jjs| ==> current_row_jjs[j1] < current_row_jjs[k1]

                invariant forall i1 :: 0 <= i1 < |new_indptr|-1 ==>
                    forall j1, k1 :: new_indptr[|new_indptr|-1] <= j1 < k1 < kk ==> new_indices[j1] < new_indices[k1] 
                invariant Canonical(new_indices, new_indptr + [kk])

                invariant forall j1 :: 0 <= j1 < |current_row_jjs| ==> getX(this.indices, this.indptr, current_row_jjs[j1]) == i + ir0

                invariant forall j1 :: 0 <= j1 < |current_row_jjs| ==> this.data[current_row_jjs[j1]] == new_data[new_indptr[|new_indptr|-1] + j1]
                invariant forall j1 :: row_start <= j1 < jj ==> ((this.indices[j1] >= ic0) && (this.indices[j1] < ic1) <==> j1 in current_row_jjs)
            
                invariant IsHeadMatrixWithData(prev_data, prev_indices, prev_indptr, new_data, new_indices, new_indptr + [kk])
            {
                if ((this.indices[jj] >= ic0) && (this.indices[jj] < ic1)) {
                    new_indices := new_indices + [this.indices[jj] - ic0];
                    new_data := new_data + [this.data[jj]];
                    kk := kk + 1;

                    current_row_jjs := current_row_jjs + [jj];
                }

                jj := jj + 1;

                // This proves that if the old matrix is canonical, the new matrix is also canonical
                forall j1, k1 | new_indptr[|new_indptr|-1] <= j1 < k1 < kk
                    ensures new_indices[j1] < new_indices[k1]
                {
                    var j2, k2 := j1 - new_indptr[|new_indptr|-1], k1 - new_indptr[|new_indptr|-1];
                    assert current_row_jjs[j2] < current_row_jjs[k2];
                    assert this.indices[current_row_jjs[j2]] - ic0 < this.indices[current_row_jjs[k2]] - ic0;
                    assert this.indices[current_row_jjs[j2]] - ic0 == new_indices[new_indptr[|new_indptr|-1] + j2];
                    assert this.indices[current_row_jjs[k2]] - ic0 == new_indices[new_indptr[|new_indptr|-1] + k2];
                    assert new_indices[j1] < new_indices[k1];
                }
            }
            new_indptr := new_indptr + [kk];

            assert forall j1 :: 0 <= j1 < |current_row_jjs| ==> this.indices[current_row_jjs[j1]] - ic0 == new_indices[new_indptr[|new_indptr|-2] + j1];
            forall y | 0 <= y < new_n_col
                ensures JExists(new_indices, new_indptr, i, y) <==> JExists(this.indices, this.indptr, i+ir0, y+ic0)
                ensures JExists(new_indices, new_indptr, i, y) ==>
                    DataAt(new_data, new_indices, new_indptr, i, y) == DataAt(this.data, this.indices, this.indptr, i+ir0, y+ic0)
            {
                JExistenceConditionForGivenXY(new_indices, new_indptr, new_n_col, i, y);
                if y in new_indices[new_indptr[|new_indptr|-2]..new_indptr[|new_indptr|-1]]
                {
                    var js := getJs(new_indices, new_indptr, |new_indptr|-2, y);
                    JExistenceConditionForGivenXY(new_indices, new_indptr, new_n_col, |new_indptr|-2, y);
                    forall j1 | j1 in js
                        ensures JExists(this.indices, this.indptr, i+ir0, y+ic0)
                        ensures DataAt(this.data, this.indices, this.indptr, i+ir0, y+ic0) == 
                            DataAt(new_data, new_indices, new_indptr, i, y)
                    {
                        assert new_indices[j1] in new_indices;
                        assert getX(new_indices, new_indptr, j1) == |new_indptr|-2 == i;
                        assert getY(new_indices, new_indptr, j1) == y;
                        XIsUniqueAndInBounds(new_indices, new_indptr, j1, |new_indptr| - 2);
                        assert 0 <= j1 - new_indptr[|new_indptr|-2] < |current_row_jjs|;

                        var j2 := current_row_jjs[j1 - new_indptr[|new_indptr|-2]];
                        assert getX(this.indices, this.indptr, j2) == i + ir0;
                        assert getY(this.indices, this.indptr, j2) == y + ic0;

                        assert this.data[j2] == new_data[j1];
                        JUniqueInCanonicalMatrix(new_indices, new_indptr, i, y, j1);
                        JUniqueInCanonicalMatrix(this.indices, this.indptr, i+ir0, y+ic0, j2);
                    }
                }
                JExistenceConditionForGivenXY(this.indices, this.indptr, this.ncols, i+ir0, y+ic0);
                if y+ic0 in this.indices[this.indptr[i+ir0]..this.indptr[i+ir0+1]]
                {
                    var js := getJs(this.indices, this.indptr, i+ir0, y+ic0);
                    JExistenceConditionForGivenXY(this.indices, this.indptr, ncols, i+ir0, y+ic0);
                    forall j1 | j1 in js
                        ensures JExists(new_indices, new_indptr, i, y)
                    {
                        XIsUniqueAndInBounds(this.indices, this.indptr, j1, i + ir0);
                        assert (this.indices[j1] >= ic0) && (this.indices[j1] < ic1);
                        assert j1 in current_row_jjs;

                        assert exists j2 :: 0 <= j2 < |current_row_jjs| && current_row_jjs[j2] == j1;
                        forall j2 | 0 <= j2 < |current_row_jjs| && current_row_jjs[j2] == j1
                            ensures JExists(new_indices, new_indptr, i, y)
                        {
                            assert y+ic0 == this.indices[j1] == this.indices[current_row_jjs[j2]] == new_indices[new_indptr[|new_indptr|-2] + j2] + ic0;
                            assert y in new_indices[new_indptr[|new_indptr|-2]..new_indptr[|new_indptr|-1]];
                        }
                    }
                }
            }

            assert forall x :: 0 <= x < i ==> forall y :: 0 <= y < new_n_col ==> (
                (JExists(prev_indices, prev_indptr, x, y) <==> JExists(this.indices, this.indptr, x+ir0, y+ic0)) &&
                (JExists(prev_indices, prev_indptr, x, y) ==>
                    DataAt(prev_data, prev_indices, prev_indptr, x, y) == DataAt(this.data, this.indices, this.indptr, x+ir0, y+ic0))
            );
            AddingRowsPreservesJExists(prev_indices, prev_indptr, new_indices, new_indptr, new_n_col);
            AddingRowsPreservesExistingData(prev_data, prev_indices, prev_indptr, new_data, new_indices, new_indptr, new_n_col);

            i := i + 1;
        }

        new_matrix := new CSRMatrix(new_data, new_indices, new_indptr, new_n_row, new_n_col);
    }

    // Implementation of _get_intXint (scipy/sparse/_compressed.py, line 654),
    // which is directly based on the above method/assertions.
    // This is the method called when the Python code uses M[x, y] to get the value at row x, column y.
    method GetIntXInt(row: int, col: int) returns (value: int)
        requires 0 <= row < nrows
        requires 0 <= col < ncols
        requires Valid()

        ensures JExists(this.indices, this.indptr, row, col) ==> DataAt(this.data, this.indices, this.indptr, row, col) == {value}
        ensures !JExists(this.indices, this.indptr, row, col) ==> value == 0
    {
        var value_matrix := this.GetSubmatrix(row, row+1, col, col+1);

        // The source code reduces the submatrix to a singular value by calling np.sum on the data array,
        // however we can show that the resulting data array always has either 0 or 1 elements, and thus the assignment below is equivalent.
        assert JExists(this.indices, this.indptr, row, col) <==> JExists(value_matrix.indices, value_matrix.indptr, 0, 0);
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



    method CopyRow(from: seq<int>) returns (ret: array<int>)
    requires |from| >= 0

    ensures ret.Length == |from|
    ensures ret[..] == from
    {
        ret := new int[|from|];
        var i := 0;
        while i < |from|
        invariant 0 <= i <= |from|
        invariant forall ii :: 0 <= ii < i ==> ret[ii] == from[ii]
        {
            ret[i] := from[i];
            i := i + 1;
        }
        assert ret[..] == from;
    }


    method AddVals(from: seq<int>, start: int) returns (ret: array<int>)
    requires |from| == ncols
    requires |from| >= 0
    requires 0 <= start < nrows
    requires Valid()

    ensures ret.Length == |from|

    // main target of verification: ensures that the output row is the sum of the matrix rol and CSR row by making sures that
    // 1. all data with column index that is not in CSR row indices remains the same as the matrix
    // 2. all data with column index that is in CSR row indices equals to the sum of the matrix data and CSR data
    ensures forall jj :: 0 <= jj < |from| && 
            ( forall ii :: indptr[start] <= ii < indptr[start+1] ==> jj != indices[ii]) ==> ret[jj] == from[jj]
    ensures forall jj :: indptr[start] <= jj < indptr[start+1] ==> ret[indices[jj]] == from[indices[jj]] + data[jj]
    {
        
        ret := new int[|from|];
        var i := 0;
        while i < |from|
        invariant 0 <= i <= |from|
        invariant forall ii :: 0 <= ii < i ==> ret[ii] == from[ii]
        {
            ret[i] := from[i];
            i := i + 1;
        }
        assert ret[..] == from;
        assert forall ii :: 0 <= ii < ret.Length ==> ret[ii] == from[ii];
        assert ret.Length == |from| == ncols;


        var j := indptr[start];
        while j < indptr[start+1]
        invariant indptr[start] <= j <= indptr[start+1]
        invariant forall jj :: 0 <= jj < |from| && 
                                    ( forall ii :: indptr[start] <= ii < indptr[start+1] ==> jj != indices[ii]) ==> ret[jj] == from[jj]
        invariant forall jj :: j <= jj < indptr[start+1] ==> ret[indices[jj]] == from[indices[jj]]
        invariant forall jj :: indptr[start] <= jj < j ==> ret[indices[jj]] == from[indices[jj]] + data[jj]
        {
            ret[indices[j]] :=  from[indices[j]] + data[j];
            assert ret[indices[j]] ==  from[indices[j]] + data[j];
            j := j + 1;
        }
    }


// verifying function csr_todense, which takes in a CSR matrix and a normal matrix, outputs the sum of two matrice
// source code: scipy/scipy/sparse/sparsetools/csr.h line 270
    method CsrToDense(m: Matrix) returns (ret: Matrix)
    requires Valid()
    requires isMatrix(m)

    // requires the shape of two input matrices match
    requires m.rows == nrows && m.columns == ncols

    ensures isMatrix(ret)
    ensures Valid()
    ensures ret.rows == m.rows && ret.columns == m.columns
    ensures forall ix :: 0 <= ix < nrows ==> (
                forall jj :: indptr[ix] <= jj < indptr[ix+1] ==> ret.vals[ix][indices[jj]] == m.vals[ix][indices[jj]] + data[jj] &&
                forall jj :: 0 <= jj < ncols && 
                ( forall ii :: indptr[ix] <= ii < indptr[ix+1] ==> jj != indices[ii]) ==> ret.vals[ix][jj] == m.vals[ix][jj]
            )
    {
        var i := 0;
        ghost var originalM := m;
        var ret_data := new seq<int>[nrows];
        
        while i < nrows 
        invariant 0 <= i <= nrows
        invariant m.vals == originalM.vals
        invariant ret_data.Length == nrows
        invariant forall ii :: 0 <= ii < i ==> |ret_data[ii]| == ncols
        invariant forall ix :: 0 <= ix < i ==> (
            forall jj :: indptr[ix] <= jj < indptr[ix+1] ==> ret_data[ix][indices[jj]] == m.vals[ix][indices[jj]] + data[jj] &&
            forall jj :: 0 <= jj < ncols && 
            ( forall ii :: indptr[ix] <= ii < indptr[ix+1] ==> jj != indices[ii]) ==> ret_data[ix][jj] == m.vals[ix][jj]
        )
        {
            var row := AddVals(m.vals[i], i);
            assert row.Length == ncols;
            ret_data[i] := row[..];
            assert |ret_data[i]| == ncols;
            i := i+1;
        }
        var ret_seq_data := ret_data[..];
        ret := Matrice(ret_seq_data, nrows, ncols);
    }
}



method Main()
{
    var indptr := [0, 2, 3, 6];
    var indices := [0, 2, 2, 0, 1, 2];
    var data := [1, 2, 3, 4, 5, 6];
    var matrix := new CSRMatrix(data, indices, indptr, 3, 3);
    // matrix:
    // [ 1  0  2  
    //   0  0  3
    //   4  5  6 ]

    var new_matrix := matrix.GetSubmatrix(0, 1, 0, 1);
    var expected := new CSRMatrix([1], [0], [0, 1], 1, 1);
    // expected
    // [ 1 ]
    assert |expected.data| == 1;
    assert expected.data[0] == 1;

    print new_matrix.data, "\n";
    print new_matrix.indices, "\n";
    print new_matrix.indptr, "\n";

    var value1 := matrix.GetIntXInt(0, 0);
    assert indices[indptr[0]..indptr[1]] == [0, 2];
    assert 0 in matrix.indices[matrix.indptr[0]..matrix.indptr[1]];
    assert value1 == 1;

    var value2 := matrix.GetIntXInt(1, 1);
    assert value2 == 0;

    var value3 := matrix.GetIntXInt(2, 1);
    assert indices[indptr[2]..indptr[3]] == [0, 1, 2];
    assert 1 in matrix.indices[matrix.indptr[2]..matrix.indptr[3]];
    assert value3 == 5;


    var m_data := [[1, 0, 0], [0, 0, 0], [0, 0, 0]];
    var m_rows := 3;
    var m_cols := 3;
    var m := Matrice(m_data, m_rows, m_cols);

    var m_sum := matrix.CsrToDense(m);
    assert |m_sum.vals| == 3;
    assert |m_sum.vals[0]| == 3;
    assert m_sum.vals[0][0] == 2;
    assert m_sum.vals[0][1] == 0;
    // expected
    // 2 0 2
    // 0 0 3
    // 4 5 6
}
