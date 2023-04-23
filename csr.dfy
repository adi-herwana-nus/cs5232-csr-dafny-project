
predicate ValidCSRIndex(indices: seq<int>, indptr: seq<int>) 
{
    |indptr| >= 1 &&
    indptr[0] == 0 &&
    indptr[|indptr| - 1] == |indices| &&
    (forall i :: 0 <= i < |indices| ==> 0 <= indices[i]) &&
    (forall i :: 0 <= i < |indptr| - 1 ==> 0 <= indptr[i] <= |indices|) &&
    (forall i, j :: 0 <= i < j < |indptr| ==> indptr[i] <= indptr[j])
}

predicate Unique(indices: seq<int>, indptr: seq<int>)
    requires ValidCSRIndex(indices, indptr)
{
    forall row :: 0 <= row < |indptr|-1 ==> forall i,j :: indptr[row] <= i < j < indptr[row+1] ==> indices[i] != indices[j]
}

predicate method Canonical(indices: seq<int>, indptr: seq<int>)
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
{
    set j | 0 <= j < |indices| && getX(indices, indptr, j) == x && getY(indices, indptr, j) == y
}

predicate JExists(indices: seq<int>, indptr: seq<int>, x: int, y: int)
    requires ValidCSRIndex(indices, indptr)
    requires Unique(indices, indptr)
{
    |getJs(indices, indptr, x, y)| == 1
}

function DataAt(data: seq<int>, indices: seq<int>, indptr: seq<int>, x: int, y: int): set<int>
    requires |data| == |indices|
    requires ValidCSRIndex(indices, indptr)
    requires Unique(indices, indptr)
{
    set j | j in getJs(indices, indptr, x, y) :: data[j]
}

lemma XYUniqueInUniqueMatrix(indices: seq<int>, indptr: seq<int>, j1: int, j2: int)
    requires ValidCSRIndex(indices, indptr)
    requires Unique(indices, indptr)
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
            assert indptr[x] <= j1 < j2 < indptr[x+1] ==> indices[j1] != indices[j2];
        }
        else
        {
            assert indptr[x] <= j2 < j1 < indptr[x+1] ==> indices[j2] != indices[j1];
        }
        assert getY(indices, indptr, j1) == indices[j1] != indices[j2] == getY(indices, indptr, j2);
        assert false;
    }
}

lemma JUniqueInUniqueMatrix(indices: seq<int>, indptr: seq<int>, x: int, y: int, j: int)
    requires ValidCSRIndex(indices, indptr)
    requires Unique(indices, indptr)
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
            XYUniqueInUniqueMatrix(indices, indptr, j, j2);
        }
    }
}

lemma DataUniqueInUniqueMatrix(data: seq<int>, indices: seq<int>, indptr: seq<int>, x: int, y: int, j: int)
    requires ValidCSRIndex(indices, indptr)
    requires Unique(indices, indptr)
    requires 0 <= j < |indices|
    requires |data| == |indices|
    requires getX(indices, indptr, j) == x
    requires getY(indices, indptr, j) == y

    ensures DataAt(data, indices, indptr, x, y) == {data[j]}
{
    JUniqueInUniqueMatrix(indices, indptr, x, y, j);
}

lemma JExistenceConditionForGivenXY(indices: seq<int>, indptr: seq<int>, ncols: int, x: int, y: int)
    requires ValidCSRIndex(indices, indptr)
    requires Unique(indices, indptr)
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
            JUniqueInUniqueMatrix(indices, indptr, x, y, j);
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
    requires Unique(indices, indptr)
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
                JUniqueInUniqueMatrix(indices, indptr, x, y, j);
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
    requires Unique(indices, indptr)
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
    requires Unique(indices1, indptr1)
    requires ValidCSRIndex(indices2, indptr2)
    requires Unique(indices2, indptr2)
    requires IsHeadMatrix(indices1, indptr1, indices2, indptr2)

    ensures forall x, y :: 0 <= x < |indptr1| - 1 && 0 <= y < ncols ==> (
        JExists(indices1, indptr1, x, y) <==> JExists(indices2, indptr2, x, y)
    )
{
    forall x, y | 0 <= x < |indptr1| - 1 && 0 <= y < ncols
        ensures JExists(indices1, indptr1, x, y) <==> JExists(indices2, indptr2, x, y)
    {
        JExistenceConditionForGivenXY(indices1, indptr1, ncols, x, y);
        JExistenceConditionForGivenXY(indices2, indptr2, ncols, x, y);
    }
}

lemma AddingRowsPreservesExistingData(data1: seq<int>, indices1: seq<int>, indptr1: seq<int>, data2: seq<int>, indices2: seq<int>, indptr2: seq<int>, ncols: int)
    requires ValidCSRIndex(indices1, indptr1)
    requires Unique(indices1, indptr1)
    requires |data1| == |indices1|
    requires ValidCSRIndex(indices2, indptr2)
    requires Unique(indices2, indptr2)
    requires |data2| == |indices2|
    requires IsHeadMatrixWithData(data1, indices1, indptr1, data2, indices2, indptr2)

    ensures forall x, y :: 0 <= x < |indptr1| - 1 && 0 <= y < ncols ==> (
        (JExists(indices1, indptr1, x, y) ==>
            DataAt(data1, indices1, indptr1, x, y) == DataAt(data2, indices2, indptr2, x, y))
    )
{
    AddingRowsPreservesJExists(indices1, indptr1, indices2, indptr2, ncols);
    forall x,y | 0 <= x < |indptr1| - 1 && 0 <= y < ncols
        ensures (JExists(indices1, indptr1, x, y) ==>
                DataAt(data1, indices1, indptr1, x, y) == DataAt(data2, indices2, indptr2, x, y))
    {
        if JExists(indices1, indptr1, x, y) 
        {
            forall j | j in getJs(indices1, indptr1, x, y)
                ensures DataAt(data1, indices1, indptr1, x, y) == DataAt(data2, indices2, indptr2, x, y)
            {
                AddingRowsPreservesExistingPositions(indices1, indptr1, indices2, indptr2);
                DataUniqueInUniqueMatrix(data1, indices1, indptr1, x, y, j);
                assert DataAt(data1, indices1, indptr1, x, y) == {data1[j]};
                assert getX(indices2, indptr2, j) == x;
                assert getY(indices2, indptr2, j) == y;
                JUniqueInUniqueMatrix(indices2, indptr2, x, y, j);
                assert DataAt(data2, indices2, indptr2, x, y) == {data2[j]};
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
        requires Unique(indices, indptr)
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
        Unique(this.indices, this.indptr) &&
        RowColValid() &&
        // Putting the existence condition in the predicate minimizes the need for repetitive assertions elsewhere,
        // even if it can be proven using the above predicates.
        forall x, y :: 0 <= x < |indptr| - 1 && 0 <= y < ncols ==>
            (JExists(indices, indptr, x, y) <==> y in indices[indptr[x]..indptr[x+1]])
    }

    predicate RowColValid()
        reads this
    {
        |indptr| == nrows + 1 && 0 <= ncols && forall j :: 0 <= j < |indices| ==> indices[j] < ncols
    }
}
