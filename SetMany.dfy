// Implementation of _set_many (scipy/sparse/_compressed.py, line 899)
// Inserts new nonzero values at coordinates specified by each element of sequences (i, j), 
// overwriting entries in the matrix if they already exist.

include "csr.dfy"
include "SampleOffsets.dfy"

// Our target precondition:
// 1. For each valid (x1, y1) NOT in the input, if the old matrix stores a value for (x1, y1) then the new matrix stores the same value there;
// 2. For each valid (x1, y1) NOT in the input, if the old matrix does NOT store a value for (x1, y1) then neither will the new matrix;
// 3. For each valid (x1, y1) in the input, the new matrix stores a value at (x1, y1) which is equal to the corresponding input data array element.
twostate predicate SetManyTarget(matrix: CSRMatrix, i: seq<int>, j: seq<int>, x: seq<int>)
    reads matrix

    requires matrix.Valid()
    requires ValidCSRIndex(old(matrix.indices), old(matrix.indptr))
    requires Unique(old(matrix.indices), old(matrix.indptr))
    requires |old(matrix.data)| == |old(matrix.indices)|

    requires |i| == |j| == |x| >= 1
    requires forall n :: 0 <= n < |i| ==> 0 <= i[n] < matrix.nrows && 0 <= j[n] < matrix.ncols
    // For now assume that the input is properly sorted along the major axis and that there are no duplicates
    // (the source implementation sorts them before insertion)
    requires forall i1, j1 :: 0 <= i1 < j1 < |i| ==> i[i1] < i[j1] || (i[i1] == i[j1] && j[i1] != j[j1])
{
    (forall x1, y1 :: 0 <= x1 < matrix.nrows && 0 <= y1 < matrix.ncols && !XYInInput(i, j, x1, y1) ==> (
        JExists(old(matrix.indices), old(matrix.indptr), x1, y1) ==> 
            (JExists(matrix.indices, matrix.indptr, x1, y1) && DataAt(matrix.data, matrix.indices, matrix.indptr, x1, y1) ==
                DataAt(old(matrix.data), old(matrix.indices), old(matrix.indptr), x1, y1))
    )) &&
    (forall x1, y1 :: 0 <= x1 < matrix.nrows && 0 <= y1 < matrix.ncols && !XYInInput(i, j, x1, y1) ==> (
        !JExists(old(matrix.indices), old(matrix.indptr), x1, y1) ==> 
            !JExists(matrix.indices, matrix.indptr, x1, y1)
    )) &&
    forall k :: 0 <= k < |i| ==>
        JExists(matrix.indices, matrix.indptr, i[k], j[k]) && DataAt(matrix.data, matrix.indices, matrix.indptr, i[k], j[k]) == {x[k]}
}

predicate XYInInput(i: seq<int>, j: seq<int>, x: int, y: int)
    requires |i| == |j|
{
    exists k :: 0 <= k < |i| && i[k] == x && j[k] == y
}



// Implementation of _insert_many (scipy/sparse/_compressed.py, line 958)
// Inserts new nonzero values at coordinates specified by (i, j)
// For our use case (in setter function), we can assume none of these entries are already in the matrix.
// Due to this inner function's complexity, we define its preconditions and postconditions abstractly here and assume they are true.

method {:axiom} InsertMany(matrix: CSRMatrix, i: seq<int>, j: seq<int>, x: seq<int>)
    modifies matrix
    requires |i| == |j| == |x| >= 1
    requires matrix.Valid()
    requires forall n :: 0 <= n < |i| ==> 0 <= i[n] < matrix.nrows && 0 <= j[n] < matrix.ncols
    requires forall i1, j1 :: 0 <= i1 < j1 < |i| ==> i[i1] <= i[j1] || (i[i1] == i[j1] && j[i1] != j[j1])

    // For our use case (proving _set_many), we can assume that the CSR matrix and input array have no places in common.
    requires forall x1, y1 :: 0 <= x1 < matrix.nrows && 0 <= y1 < matrix.ncols ==>
        (XYInInput(i, j, x1, y1) ==> !JExists(matrix.indices, matrix.indptr, x1, y1))

    ensures matrix.Valid()
    ensures matrix.nrows == old(matrix.nrows)
    ensures matrix.ncols == old(matrix.ncols)
    ensures forall x1, y1 :: 0 <= x1 < matrix.nrows && 0 <= y1 < matrix.ncols ==> (
        ((JExists(old(matrix.indices), old(matrix.indptr), x1, y1) && !XYInInput(i, j, x1, y1)) ==>
            JExists(matrix.indices, matrix.indptr, x1, y1) &&
            (DataAt(matrix.data, matrix.indices, matrix.indptr, x1, y1) == DataAt(old(matrix.data), old(matrix.indices), old(matrix.indptr), x1, y1))) &&
        ((!JExists(old(matrix.indices), old(matrix.indptr), x1, y1) && !XYInInput(i, j, x1, y1)) ==> 
            !JExists(matrix.indices, matrix.indptr, x1, y1))
    )
    ensures forall k :: 0 <= k < |i| ==>
        (JExists(matrix.indices, matrix.indptr, i[k], j[k]) && DataAt(matrix.data, matrix.indices, matrix.indptr, i[k], j[k]) == {x[k]})



lemma UnwrapPostcondition(P: bool, A: bool, B: bool, C: bool, D: bool)
    requires P
    requires P ==> (((A && B) ==> (C && D)) && ((!A && B) ==> (!C)))
    requires A
    requires B
    ensures C
    ensures D
{
    var E := C && D;
    assert P ==> (((A && B) ==> E) && ((!A && B) ==> (!C)));
    if P {
        assert ((A && B) ==> E) && ((!A && B) ==> (!C));
        assert (A && B) ==> E;
    }
}

method SetMany(matrix: CSRMatrix, i: seq<int>, j: seq<int>, x: seq<int>)
    modifies matrix

    requires |i| == |j| == |x| >= 1
    requires forall n :: 0 <= n < |i| ==> 0 <= i[n] < matrix.nrows && 0 <= j[n] < matrix.ncols
    // For now assume that the input is properly sorted along the major axis and that there are no duplicates
    // (the source implementation sorts them before insertion)
    requires forall i1, j1 :: 0 <= i1 < j1 < |i| ==> i[i1] < i[j1] || (i[i1] == i[j1] && j[i1] != j[j1])

    requires matrix.Valid()

    ensures matrix.Valid()
    ensures matrix.nrows == old(matrix.nrows)
    ensures matrix.ncols == old(matrix.ncols)
    ensures SetManyTarget(matrix, i, j, x)
{

    var offsets := SampleOffsets(matrix, i, j);
    forall l1, l2 | 0 <= l1 < l2 < |offsets| && offsets[l1] == offsets[l2] > 0
        ensures false
    {
        assert getX(matrix.indices, matrix.indptr, offsets[l1]) == i[l1];
        assert getX(matrix.indices, matrix.indptr, offsets[l2]) == i[l2];
        assert getY(matrix.indices, matrix.indptr, offsets[l1]) == j[l1];
        assert getY(matrix.indices, matrix.indptr, offsets[l2]) == j[l2];
    }
    // these variables represent the resulting arrays from numpy slicing operations with mask and ~mask
    // For example, offsets_mask == offsets[mask] == offsets[offsets > -1], etc.
    var offsets_mask: seq<int>, offsets_negate_mask: seq<int> := [], [];
    var i_mask: seq<int>, i_negate_mask: seq<int> := [], [];
    var j_mask: seq<int>, j_negate_mask: seq<int> := [], [];
    var x_mask: seq<int>, x_negate_mask: seq<int> := [], [];

    var mask_mapping: map<int, int>, negate_mask_mapping: map<int, int> := map[], map[];

    if -1 !in offsets
    {
        // only affects existing non-zero cells
        offsets_mask, i_mask, j_mask, x_mask := offsets, i, j, x;
    }
    else 
    {
        // replace where possible

        // This performs the slicing operations.
        var k_mask := 0;
        var mask_indices: seq<int>, negate_mask_indices: seq<int> := [], [];

        while k_mask < |offsets|
            invariant 0 <= k_mask <= |offsets|
            invariant |mask_indices| + |negate_mask_indices| == k_mask
            invariant forall k1 :: 0 <= k1 < |mask_indices| ==> 0 <= mask_indices[k1] < k_mask
            invariant forall k1, k2 :: 0 <= k1 < k2 < |mask_indices| ==> mask_indices[k1] < mask_indices[k2]
            invariant forall k1 :: 0 <= k1 < |negate_mask_indices| ==> 0 <= negate_mask_indices[k1] < k_mask
            invariant forall k1, k2 :: 0 <= k1 < k2 < |negate_mask_indices| ==> negate_mask_indices[k1] < negate_mask_indices[k2]
            invariant forall k1 :: 0 <= k1 < k_mask ==> (k1 in mask_indices <==> 0 <= offsets[k1] <= |matrix.indices|)
            invariant forall k1 :: 0 <= k1 < k_mask ==> (k1 in mask_indices <==> k1 !in negate_mask_indices)
        {
            if offsets[k_mask] > -1
            {
                mask_indices := mask_indices + [k_mask];
            }
            else
            {
                negate_mask_indices := negate_mask_indices + [k_mask];
            }
            k_mask := k_mask + 1;
        }

        offsets_mask := seq(|mask_indices|, k requires 0 <= k < |mask_indices| => offsets[mask_indices[k]]);
        i_mask := seq(|mask_indices|, k requires 0 <= k < |mask_indices| => i[mask_indices[k]]);
        j_mask := seq(|mask_indices|, k requires 0 <= k < |mask_indices| => j[mask_indices[k]]);
        x_mask := seq(|mask_indices|, k requires 0 <= k < |mask_indices| => x[mask_indices[k]]);

        offsets_negate_mask := seq(|negate_mask_indices|, k requires 0 <= k < |negate_mask_indices| => offsets[negate_mask_indices[k]]);
        i_negate_mask := seq(|negate_mask_indices|, k requires 0 <= k < |negate_mask_indices| => i[negate_mask_indices[k]]);
        j_negate_mask := seq(|negate_mask_indices|, k requires 0 <= k < |negate_mask_indices| => j[negate_mask_indices[k]]);
        x_negate_mask := seq(|negate_mask_indices|, k requires 0 <= k < |negate_mask_indices| => x[negate_mask_indices[k]]);

        forall x1, y1 | 0 <= x1 < matrix.nrows && 0 <= y1 < matrix.ncols
            ensures XYInInput(i, j, x1, y1) ==> (
                (XYInInput(i_mask, j_mask, x1, y1) && JExists(matrix.indices, matrix.indptr, x1, y1)) ||
                (XYInInput(i_negate_mask, j_negate_mask, x1, y1) && !JExists(matrix.indices, matrix.indptr, x1, y1))
            )
        {
            if XYInInput(i, j, x1, y1)
            {
                forall k1 | 0 <= k1 < |offsets| && i[k1] == x1 && j[k1] == y1
                    ensures (XYInInput(i_mask, j_mask, x1, y1) && JExists(matrix.indices, matrix.indptr, x1, y1)) ||
                    (XYInInput(i_negate_mask, j_negate_mask, x1, y1) && !JExists(matrix.indices, matrix.indptr, x1, y1))
                {
                    if k1 in mask_indices
                    {
                        forall k2 | 0 <= k2 < |mask_indices| && mask_indices[k2] == k1
                            ensures XYInInput(i_mask, j_mask, x1, y1)
                            ensures JExists(matrix.indices, matrix.indptr, x1, y1)
                        {
                            assert i_mask[k2] == x1 && j_mask[k2] == y1;
                        }
                    }
                    else
                    {
                        forall k2 | 0 <= k2 < |negate_mask_indices| && negate_mask_indices[k2] == k1
                            ensures XYInInput(i_negate_mask, j_negate_mask, x1, y1)
                            ensures !JExists(matrix.indices, matrix.indptr, x1, y1)
                        {
                            assert i_negate_mask[k2] == x1 && j_negate_mask[k2] == y1;
                        }
                    }
                }
            }
        }
    }

    // Update all existing cell values (lines 920 and 929 in source code)
    var updated_data := matrix.data;
    var updated_indices := matrix.indices;
    var updated_indptr := matrix.indptr;

    var k_update := 0;
    while k_update < |offsets_mask|
        invariant 0 <= k_update <= |offsets_mask|
        invariant |updated_data| == |updated_indices|
        invariant forall l :: 0 <= l < |updated_indices| && l !in offsets_mask ==> updated_data[l] == matrix.data[l]
        invariant forall l :: 0 <= l < |updated_indices| && l in offsets_mask[k_update..] ==> updated_data[l] == matrix.data[l]

        invariant forall k1 :: 0 <= k1 < k_update ==> DataAt(updated_data, updated_indices, updated_indptr, i_mask[k1], j_mask[k1]) == {x_mask[k1]}
    {
        var old_updated_data := updated_data;

        updated_data := updated_data[offsets_mask[k_update] := x_mask[k_update]];

        assert forall k1 :: 0 <= k1 < |updated_data| && k1 != offsets_mask[k_update] ==> updated_data[k1] == old_updated_data[k1];
        forall k1 | 0 <= k1 <= k_update
            ensures DataAt(updated_data, updated_indices, updated_indptr, i_mask[k1], j_mask[k1]) == {x_mask[k1]}
        {
            assert getX(updated_indices, updated_indptr, offsets_mask[k1]) == i_mask[k1];
            assert getY(updated_indices, updated_indptr, offsets_mask[k1]) == j_mask[k1];
            DataUniqueInUniqueMatrix(updated_data, updated_indices, updated_indptr, i_mask[k1], j_mask[k1], offsets_mask[k1]);
            if k1 == k_update
            {
                assert DataAt(updated_data, updated_indices, updated_indptr, i_mask[k_update], j_mask[k_update]) == {x_mask[k_update]};
            }
            else
            {
                assert DataAt(updated_data, updated_indices, updated_indptr, i_mask[k1], j_mask[k1]) == {x_mask[k1]};
            }
        }

        k_update := k_update + 1;
    }
    matrix.data := updated_data;
    matrix.indices := updated_indices;
    matrix.indptr := updated_indptr;
    label U:
    // Future calls to old@U(matrix.*) will pull the intermediate value of the matrix
    // (i.e. after updates to existing elements but before insertions of new elements)

    forall x1, y1 | 0 <= x1 < matrix.nrows && 0 <= y1 < matrix.ncols
        ensures !JExists(old(matrix.indices), old(matrix.indptr), x1, y1) ==> !JExists(matrix.indices, matrix.indptr, x1, y1)
        ensures JExists(matrix.indices, matrix.indptr, x1, y1) && (!XYInInput(i, j, x1, y1)) ==> 
            (JExists(updated_indices, updated_indptr, x1, y1) && DataAt(updated_data, updated_indices, updated_indptr, x1, y1) ==
                DataAt(matrix.data, matrix.indices, matrix.indptr, x1, y1))
    {
        if JExists(matrix.indices, matrix.indptr, x1, y1)
        {
            assert JExists(updated_indices, updated_indptr, x1, y1);
            if !XYInInput(i, j, x1, y1)
            {
                assert !XYInInput(i_mask, j_mask, x1, y1);
                forall j1 | 0 <= j1 < |matrix.indices| && getX(matrix.indices, matrix.indptr, j1) == x1 && getY(matrix.indices, matrix.indptr, j1) == y1
                    ensures DataAt(updated_data, updated_indices, updated_indptr, x1, y1) == DataAt(matrix.data, matrix.indices, matrix.indptr, x1, y1);
                {
                    assert j1 !in offsets_mask;
                    assert updated_data[j1] == matrix.data[j1];
                    assert DataAt(updated_data, updated_indices, updated_indptr, x1, y1) == DataAt(matrix.data, matrix.indices, matrix.indptr, x1, y1);
                }
            }
        }
    }

    if |offsets_negate_mask| >= 1
    {
        InsertMany(matrix, i_negate_mask, j_negate_mask, x_negate_mask);
        assert forall x1, y1 :: 0 <= x1 < matrix.nrows && 0 <= y1 < matrix.ncols ==> (
            ((JExists(old@U(matrix.indices), old@U(matrix.indptr), x1, y1) && !XYInInput(i_negate_mask, j_negate_mask, x1, y1)) ==>
                JExists(matrix.indices, matrix.indptr, x1, y1) &&
                (DataAt(matrix.data, matrix.indices, matrix.indptr, x1, y1) == DataAt(old@U(matrix.data), old@U(matrix.indices), old@U(matrix.indptr), x1, y1))) &&
            ((!JExists(old@U(matrix.indices), old@U(matrix.indptr), x1, y1) && !XYInInput(i_negate_mask, j_negate_mask, x1, y1)) ==> 
                !JExists(matrix.indices, matrix.indptr, x1, y1))
        );
    }

    forall x1, y1 | 0 <= x1 < matrix.nrows && 0 <= y1 < matrix.ncols && !XYInInput(i, j, x1, y1)
        ensures JExists(old(matrix.indices), old(matrix.indptr), x1, y1) ==> 
            (JExists(matrix.indices, matrix.indptr, x1, y1) && DataAt(matrix.data, matrix.indices, matrix.indptr, x1, y1) ==
                DataAt(old(matrix.data), old(matrix.indices), old(matrix.indptr), x1, y1))
        ensures !JExists(old(matrix.indices), old(matrix.indptr), x1, y1) ==> 
            (!JExists(matrix.indices, matrix.indptr, x1, y1))
    {
        if JExists(old(matrix.indices), old(matrix.indptr), x1, y1)
        {
            assert JExists(old@U(matrix.indices), old@U(matrix.indptr), x1, y1);
            assert !XYInInput(i_negate_mask, j_negate_mask, x1, y1);
            assert JExists(matrix.indices, matrix.indptr, x1, y1) &&
                (DataAt(matrix.data, matrix.indices, matrix.indptr, x1, y1) == DataAt(old@U(matrix.data), old@U(matrix.indices), old@U(matrix.indptr), x1, y1));
        }
        else
        {
            assert !JExists(old@U(matrix.indices), old@U(matrix.indptr), x1, y1);
            assert !XYInInput(i_negate_mask, j_negate_mask, x1, y1);
            assert !JExists(matrix.indices, matrix.indptr, x1, y1);
        }
    }

    forall k | 0 <= k < |i|
        ensures JExists(matrix.indices, matrix.indptr, i[k], j[k]) && DataAt(matrix.data, matrix.indices, matrix.indptr, i[k], j[k]) == {x[k]}
    {
        var x1, y1 := i[k], j[k];
        assert 0 <= x1 < matrix.nrows && 0 <= y1 < matrix.ncols;
        if JExists(old(matrix.indices), old(matrix.indptr), x1, y1) 
        {
            assert JExists(old@U(matrix.indices), old@U(matrix.indptr), x1, y1) &&
                DataAt(old@U(matrix.data), old@U(matrix.indices), old@U(matrix.indptr), x1, y1) == {x[k]};
           
            assert JExists(old@U(matrix.indices), old@U(matrix.indptr), x1, y1);
            assert !XYInInput(i_negate_mask, j_negate_mask, x1, y1);
            UnwrapPostcondition(
                0 <= x1 < matrix.nrows && 0 <= y1 < matrix.ncols,
                JExists(old@U(matrix.indices), old@U(matrix.indptr), x1, y1),
                !XYInInput(i_negate_mask, j_negate_mask, x1, y1),
                JExists(matrix.indices, matrix.indptr, x1, y1),
                DataAt(matrix.data, matrix.indices, matrix.indptr, x1, y1) == DataAt(old@U(matrix.data), old@U(matrix.indices), old@U(matrix.indptr), x1, y1)
            );
            assert JExists(matrix.indices, matrix.indptr, x1, y1);
            assert DataAt(matrix.data, matrix.indices, matrix.indptr, x1, y1) == DataAt(old@U(matrix.data), old@U(matrix.indices), old@U(matrix.indptr), x1, y1);
            assert DataAt(matrix.data, matrix.indices, matrix.indptr, i[k], j[k]) == {x[k]};
        }
        else
        {
            assert !JExists(old@U(matrix.indices), old@U(matrix.indptr), x1, y1);
            assert XYInInput(i_negate_mask, j_negate_mask, x1, y1);
            assert JExists(matrix.indices, matrix.indptr, x1, y1);
            assert DataAt(matrix.data, matrix.indices, matrix.indptr, i[k], j[k]) == {x[k]};
        }
    }
}
