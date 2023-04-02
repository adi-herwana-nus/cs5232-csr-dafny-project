predicate ValidCSRIndex(indices: seq<int>, indptr: seq<int>) 
    //ensures |indptr| >= 3 ==> ValidCSRIndex(indices[..indptr[|indptr|-2]], indptr[..|indptr|-1])
{
    |indptr| >= 1 &&
    indptr[0] == 0 &&
    indptr[|indptr| - 1] == |indices| &&
    (forall i :: 0 <= i < |indptr| - 1 ==> 0 <= indptr[i] <= |indices|) &&
    (forall i, j :: 0 <= i < j < |indptr| ==> indptr[i] <= indptr[j])
}

predicate ValidCSRIndexClone(indices: seq<int>, indptr: seq<int>) 
    //ensures |indptr| >= 3 ==> ValidCSRIndex(indices[..indptr[|indptr|-2]], indptr[..|indptr|-1])
{
    |indptr| >= 1 &&
    indptr[0] == 0 &&
    indptr[|indptr| - 1] == |indices| &&
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

// method getXMethod(indices: seq<int>, indptr: seq<int>, j: int) returns (x: int)
//     requires ValidCSRIndex(indices, indptr)
//     requires 0 <= j < |indices|

//     ensures 0 <= x <= |indptr| - 2
//     ensures indptr[x] <= j < indptr[x+1]
//     ensures forall x1 :: 0 <= x1 < x ==> j >= indptr[x1+1]
//     ensures forall x1 :: x < x1 <= |indptr|-2 ==> j < indptr[x1]
//     ensures forall x1 :: 0 <= x1 <= |indptr| - 2 ==> ((indptr[x1] <= j < indptr[x1+1]) <==> (x1 == x))

//     ensures x == getX(indices, indptr, j)
// {
//     x := |indptr| - 2;
//     assert indptr[x+1] == |indices|;
//     while x > 0 && indptr[x] > j 
//         invariant 0 <= x <= |indptr| - 2
//         invariant indptr[x+1] > j
//     {
//         x := x - 1;
//     }

//     ghost var x1 := getX(indices, indptr, j);
//     XIsUniqueAndInBounds(indices, indptr, j, x1);
// }

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
    }

    predicate Valid() 
        reads this
    {
        |data| == |indices| &&
        ValidCSRIndex(this.indices, this.indptr) &&
        Canonical(this.indices, this.indptr) &&
        RowColValid()
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

        // Our primary goal: for all valid x,y coordinates in the new matrix we prove that
        // 1. The new matrix stores a value for (x, y) if and only if it stores a value for (x+ir0, y+ic0); and
        // 2. If new matrix stores a value for (x, y), it is equal to the one stored at (x+ir0, y+ic0).
        ensures forall x :: 0 <= x < new_matrix.nrows ==> forall y :: 0 <= y <new_matrix.ncols ==> (
            (JExists(new_matrix.indices, new_matrix.indptr, x, y) <==> JExists(this.indices, this.indptr, x+ir0, y+ic0)) &&
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

    print new_matrix.data, "\n";
    print new_matrix.indices, "\n";
    print new_matrix.indptr, "\n";
}