// Implementation of get_csr_submatrix (scipy/sparse/sparsetools/csr.h, line 1181)
// The typical numpy-style getter M[x, y] is implemented as a special case of this method
// (where ir0 = x, ir1 = x+1, ic0 = y, ic1 = y+1).
// This implies SciPy uses an O(nnz) search algorithm to access matrix entries,
// even though an O(log(nnz)) algorithm should be possible using binary search.

include "csr.dfy"

// Our primary goal: for all valid x,y coordinates in the new matrix we prove the following:
// 1. The new matrix stores a value for (x, y) if and only if the old matrix stores a value for (x+ir0, y+ic0);
// 2. If the new matrix stores a value for (x, y), then it is equal to the value of the old matrix at (x+ir0, y+ic0).
predicate GetSubmatrixTarget(old_matrix: CSRMatrix, ir0: int, ir1: int, ic0: int, ic1: int, new_data: seq<int>, new_indices: seq<int>, new_indptr: seq<int>)
    reads old_matrix
    requires old_matrix.Valid()
    requires |new_data| == |new_indices|
    requires ValidCSRIndex(new_indices, new_indptr)
    requires Canonical(new_indices, new_indptr)
{
    forall x, y :: 0 <= x < ir1-ir0 && 0 <= y < ic1-ic0 ==> (
        (JExists(new_indices, new_indptr, x, y) <==> JExists(old_matrix.indices, old_matrix.indptr, x+ir0, y+ic0)) &&
        (JExists(new_indices, new_indptr, x, y) ==>
            DataAt(new_data, new_indices, new_indptr, x, y) == DataAt(old_matrix.data, old_matrix.indices, old_matrix.indptr, x+ir0, y+ic0))
    )
}

method GetSubmatrix(old_matrix: CSRMatrix, ir0: int, ir1: int, ic0: int, ic1: int) returns (new_matrix: CSRMatrix)
    requires 0 <= ir0 < ir1 <= old_matrix.nrows
    requires ir0 < old_matrix.nrows
    requires 0 <= ic0 < ic1 <= old_matrix.ncols
    requires ic0 < old_matrix.ncols
    requires old_matrix.Valid()

    ensures old_matrix.Valid()
    ensures new_matrix.nrows == ir1 - ir0
    ensures new_matrix.ncols == ic1 - ic0
    ensures new_matrix.Valid()

    ensures GetSubmatrixTarget(old_matrix, ir0, ir1, ic0, ic1, new_matrix.data, new_matrix.indices, new_matrix.indptr)
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
        invariant GetSubmatrixTarget(old_matrix, ir0, ir0 + i, ic0, ic1, new_data, new_indices, new_indptr)
    {
        ghost var prev_data, prev_indices, prev_indptr := new_data, new_indices, new_indptr;
        var row_start := old_matrix.indptr[ir0+i];
        var row_end   := old_matrix.indptr[ir0+i+1];

        forall jj | row_start <= jj < row_end
            ensures getX(old_matrix.indices, old_matrix.indptr, jj) == i+ir0
        {
            XIsUniqueAndInBounds(old_matrix.indices, old_matrix.indptr, jj, getX(old_matrix.indices, old_matrix.indptr, jj));
        }

        assert forall j1, k1 :: row_start <= j1 < k1 < row_end ==> old_matrix.indices[j1] < old_matrix.indices[k1];
        ghost var current_row_jjs: seq<int> := [];
        
        var jj := row_start;
        while jj < row_end
            invariant 0 <= row_start <= jj <= row_end <= |old_matrix.indices|

            invariant kk == |new_indices| == |new_data|

            invariant forall i1 :: 0 <= i1 < |new_indptr| ==> new_indptr[i1] <= kk
            invariant forall i1, j1 :: 0 <= i1 < j1 < |new_indptr| ==> new_indptr[i1] <= new_indptr[j1]
            invariant ValidCSRIndex(new_indices, new_indptr + [kk])

            invariant forall i1 :: 0 <= i1 < |new_indptr|-1 ==>
                forall j1, k1 :: new_indptr[i1] <= j1 < k1 < new_indptr[i1+1] ==> new_indices[j1] < new_indices[k1] 

            invariant forall j1 :: 0 <= j1 < |new_indices| ==> 0 <= new_indices[j1] < new_n_col

            invariant |new_indices| == new_indptr[|new_indptr|-1] + |current_row_jjs|
            invariant forall j1 :: 0 <= j1 < |current_row_jjs| ==> row_start <= current_row_jjs[j1] < jj
            invariant forall j1 :: 0 <= j1 < |current_row_jjs| ==> new_indices[new_indptr[|new_indptr|-1] + j1] == old_matrix.indices[current_row_jjs[j1]] - ic0
            invariant forall j1, k1 :: 0 <= j1 < k1 < |current_row_jjs| ==> current_row_jjs[j1] < current_row_jjs[k1]

            invariant forall i1, j1, k1 :: 0 <= i1 < |new_indptr|-1 && new_indptr[i1] <= j1 < k1 < new_indptr[i1+1] ==> new_indices[j1] < new_indices[k1]
            invariant forall j1, k1 :: new_indptr[|new_indptr|-1] <= j1 < k1 < kk ==> new_indices[j1] < new_indices[k1] 
            invariant Canonical(new_indices, new_indptr + [kk])

            invariant forall j1 :: 0 <= j1 < |current_row_jjs| ==> getX(old_matrix.indices, old_matrix.indptr, current_row_jjs[j1]) == i + ir0

            invariant forall j1 :: 0 <= j1 < |current_row_jjs| ==> old_matrix.data[current_row_jjs[j1]] == new_data[new_indptr[|new_indptr|-1] + j1]
            invariant forall j1 :: row_start <= j1 < jj ==> ((old_matrix.indices[j1] >= ic0) && (old_matrix.indices[j1] < ic1) <==> j1 in current_row_jjs)
        
            invariant IsHeadMatrixWithData(prev_data, prev_indices, prev_indptr, new_data, new_indices, new_indptr + [kk])
        {
            if ((old_matrix.indices[jj] >= ic0) && (old_matrix.indices[jj] < ic1)) {
                new_indices := new_indices + [old_matrix.indices[jj] - ic0];
                new_data := new_data + [old_matrix.data[jj]];
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
                assert old_matrix.indices[current_row_jjs[j2]] - ic0 < old_matrix.indices[current_row_jjs[k2]] - ic0;
                assert old_matrix.indices[current_row_jjs[j2]] - ic0 == new_indices[new_indptr[|new_indptr|-1] + j2];
                assert old_matrix.indices[current_row_jjs[k2]] - ic0 == new_indices[new_indptr[|new_indptr|-1] + k2];
                assert new_indices[j1] < new_indices[k1];
            }
        }
        new_indptr := new_indptr + [kk];

        assert forall j1 :: 0 <= j1 < |current_row_jjs| ==> old_matrix.indices[current_row_jjs[j1]] - ic0 == new_indices[new_indptr[|new_indptr|-2] + j1];
        forall y | 0 <= y < new_n_col
            ensures JExists(new_indices, new_indptr, i, y) <==> JExists(old_matrix.indices, old_matrix.indptr, i+ir0, y+ic0)
            ensures JExists(new_indices, new_indptr, i, y) ==>
                DataAt(new_data, new_indices, new_indptr, i, y) == DataAt(old_matrix.data, old_matrix.indices, old_matrix.indptr, i+ir0, y+ic0)
        {
            JExistenceConditionForGivenXY(new_indices, new_indptr, new_n_col, i, y);
            if y in new_indices[new_indptr[|new_indptr|-2]..new_indptr[|new_indptr|-1]]
            {
                var js := getJs(new_indices, new_indptr, |new_indptr|-2, y);
                JExistenceConditionForGivenXY(new_indices, new_indptr, new_n_col, |new_indptr|-2, y);
                forall j1 | j1 in js
                    ensures JExists(old_matrix.indices, old_matrix.indptr, i+ir0, y+ic0)
                    ensures DataAt(old_matrix.data, old_matrix.indices, old_matrix.indptr, i+ir0, y+ic0) == 
                        DataAt(new_data, new_indices, new_indptr, i, y)
                {
                    assert new_indices[j1] in new_indices;
                    assert getX(new_indices, new_indptr, j1) == |new_indptr|-2 == i;
                    assert getY(new_indices, new_indptr, j1) == y;
                    XIsUniqueAndInBounds(new_indices, new_indptr, j1, |new_indptr| - 2);
                    assert 0 <= j1 - new_indptr[|new_indptr|-2] < |current_row_jjs|;

                    var j2 := current_row_jjs[j1 - new_indptr[|new_indptr|-2]];
                    assert getX(old_matrix.indices, old_matrix.indptr, j2) == i + ir0;
                    assert getY(old_matrix.indices, old_matrix.indptr, j2) == y + ic0;

                    assert old_matrix.data[j2] == new_data[j1];
                    JUniqueInCanonicalMatrix(new_indices, new_indptr, i, y, j1);
                    JUniqueInCanonicalMatrix(old_matrix.indices, old_matrix.indptr, i+ir0, y+ic0, j2);
                }
            }
            JExistenceConditionForGivenXY(old_matrix.indices, old_matrix.indptr, old_matrix.ncols, i+ir0, y+ic0);
            if y+ic0 in old_matrix.indices[old_matrix.indptr[i+ir0]..old_matrix.indptr[i+ir0+1]]
            {
                var js := getJs(old_matrix.indices, old_matrix.indptr, i+ir0, y+ic0);
                JExistenceConditionForGivenXY(old_matrix.indices, old_matrix.indptr, old_matrix.ncols, i+ir0, y+ic0);
                forall j1 | j1 in js
                    ensures JExists(new_indices, new_indptr, i, y)
                {
                    XIsUniqueAndInBounds(old_matrix.indices, old_matrix.indptr, j1, i + ir0);
                    assert (old_matrix.indices[j1] >= ic0) && (old_matrix.indices[j1] < ic1);
                    assert j1 in current_row_jjs;

                    assert exists j2 :: 0 <= j2 < |current_row_jjs| && current_row_jjs[j2] == j1;
                    forall j2 | 0 <= j2 < |current_row_jjs| && current_row_jjs[j2] == j1
                        ensures JExists(new_indices, new_indptr, i, y)
                    {
                        assert y+ic0 == old_matrix.indices[j1] == old_matrix.indices[current_row_jjs[j2]] == new_indices[new_indptr[|new_indptr|-2] + j2] + ic0;
                        assert y in new_indices[new_indptr[|new_indptr|-2]..new_indptr[|new_indptr|-1]];
                    }
                }
            }
        }

        assert GetSubmatrixTarget(old_matrix, ir0, ir0 + i, ic0, ic1, prev_data, prev_indices, prev_indptr);
        AddingRowsPreservesJExists(prev_indices, prev_indptr, new_indices, new_indptr, new_n_col);
        AddingRowsPreservesExistingData(prev_data, prev_indices, prev_indptr, new_data, new_indices, new_indptr, new_n_col);

        i := i + 1;
    }

    new_matrix := new CSRMatrix(new_data, new_indices, new_indptr, new_n_row, new_n_col);
}
