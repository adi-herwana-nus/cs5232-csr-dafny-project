// Implementation of _insert_many (scipy/sparse/_compressed.py, line 958)
// Inserts new nonzero values at coordinates specified by (i, j)
// For our use case (in setter function), we can assume none of these entries are already in the matrix.

include "csr.dfy"

// Custom implementation for numpy.unique(ar, return_index=True) following the referenced spec here:
// https://numpy.org/doc/stable/reference/generated/numpy.unique.html
// Namely, this method returns two values:
// unique: The (sorted) unique values.
// unique_indices: The indices of the first occurrences of the unique values in the original array.
method NumpyUniqueReturnIndex(ar: seq<int>) returns (unique: seq<int>, unique_indices: seq<int>)
    ensures (set x | x in unique) == (set x | x in ar)
    ensures |unique| == |unique_indices|
    ensures forall j, k :: 0 <= j < k < |unique| ==> unique[j] < unique[k]
    ensures forall j :: 0 <= j < |unique| ==> 0 <= unique_indices[j] < |ar|
    ensures forall j :: 0 <= j < |unique| ==> ar[unique_indices[j]] == unique[j]
    ensures forall j, k :: 0 <= j < k < |unique_indices| ==> unique_indices[j] != unique_indices[k]
    ensures forall j, k :: 0 <= j < |unique| && 0 <= k < unique_indices[j] ==> ar[k] != unique[j]
{
    unique := [];
    var unique_map: map<int, int> := map[];
    var i := 0;

    while i < |ar|
        invariant 0 <= i <= |ar|
        invariant (set x | x in unique) == unique_map.Keys == (set x | x in ar[..i])
        invariant forall k, l :: 0 <= k < l < |unique| ==> unique[k] < unique[l]
        invariant forall x :: x in unique_map.Keys ==> 0 <= unique_map[x] < i
        invariant forall x :: x in unique_map.Keys ==> ar[unique_map[x]] == x
        invariant forall k, l :: 0 <= k < |unique| && 0 <= l < unique_map[unique[k]] ==> ar[l] != unique[k]
    {
        if (ar[i] !in unique)
        {
            unique_map := unique_map[ar[i] := i];
            var j := 0;
            while j < |unique| && unique[j] < ar[i]
                invariant 0 <= j <= |unique|
                invariant forall k, l :: 0 <= k < l < |unique| ==> unique[k] < unique[l]
                invariant forall k :: 0 <= k < j ==> unique[k] < ar[i]
            {
                j := j + 1;
            }
            var old_unique := unique;
            unique := unique[..j] + [ar[i]] + unique[j..];
            forall k | 0 <= k < i && ar[k] == unique[j]
                ensures false
            {
                var s1, s2 := set x | x in ar[..i], set x | x in old_unique;
                assert ar[k] in ar[..i] && ar[k] in s1;
                assert ar[k] !in old_unique && ar[k] !in s2;
                assert s1 == s2;
            }
        }
        i := i + 1;
    }
    unique_indices := seq(|unique|, j requires 0 <= j < |unique| => unique_map[unique[j]]);
}

lemma SeqSetEqualityImpliesExistence(s1: seq<int>, s2: seq<int>, x: int)
    requires (set y | y in s1) == (set y | y in s2)
    requires x in s1
    ensures x in s2
    ensures exists i2 :: 0 <= i2 < |s2| && s2[i2] == x
{
    var t1, t2 := (set y | y in s1), (set y | y in s2);
    if forall i2 :: 0 <= i2 < |s2| ==> s2[i2] != x {
        assert x !in s2;
        assert x !in t2;
        assert x !in t1;
        assert false;
    }
}

lemma SeqSetEqualityImpliesEquivalence(s1: seq<int>, s2: seq<int>, x: int)
    requires (set y | y in s1) == (set y | y in s2)
    ensures x in s1 <==> x in s2
    ensures x !in s1 <==> x !in s2
{
    if x in s1
    {
        SeqSetEqualityImpliesExistence(s1, s2, x);
    }
    if x in s2
    {
        SeqSetEqualityImpliesExistence(s2, s1, x);
    }
}

function NpDiff(a: seq<int>): seq<int>
    requires |a| >= 1
{
    seq(|a|-1, i requires 0 <= i < |a|-1 => a[i+1] - a[i])
}

function NpConcatenate(a: seq<seq<int>>): seq<int>
{
    if |a| == 0 then [] else NpConcatenate(a[..|a|-1]) + a[|a|-1]
}

lemma ShiftedSubsequenceEquality(s1: seq<int>, l1: int, u1: int, s2: seq<int>, shift: int)
    requires 0 <= l1 <= u1 <= |s1|
    requires l1 + shift >= 0
    requires u1 + shift <= |s2|
    requires forall k :: l1 <= k < u1 ==> s1[k] == s2[k + shift]
    decreases u1-l1

    ensures s1[l1..u1] == s2[l1+shift..u1+shift]
{
    if l1 == u1
    {
        assert s1[l1..u1] == s2[l1+shift..u1+shift];
    }
    else
    {
        assert forall k :: l1+1 <= k < u1 ==> s1[k] == s2[k + shift];
        ShiftedSubsequenceEquality(s1, l1+1, u1, s2, shift);
    }
}

predicate XYInInput(i: seq<int>, j: seq<int>, x: int, y: int)
    requires |i| == |j|
{
    exists k :: 0 <= k < |i| && i[k] == x && j[k] == y
}

method InsertMany(matrix: CSRMatrix, i: seq<int>, j: seq<int>, x: seq<int>)
    requires |i| == |j| == |x| >= 1
    requires matrix.Valid()

    requires forall n :: 0 <= n < |i| ==> 0 <= i[n] < matrix.nrows && 0 <= j[n] < matrix.ncols

    // For now assume that the input is properly sorted along the major axis and that there are no duplicates
    // (the source implementation sorts them before insertion)
    requires forall i1, j1 :: 0 <= i1 < j1 < |i| ==> i[i1] <= i[j1] || (i[i1] == i[j1] && j[i1] != j[j1])

    // For our use case (proving _set_many), we can assume that the CSR matrix and input array have no places in common.
    requires forall x, y :: 0 <= x < matrix.nrows && 0 <= y < matrix.ncols ==>
        (XYInInput(i, j, x, y) <==> !JExists(matrix.indices, matrix.indptr, x, y))
    ensures matrix.Valid()
{
    var indices_parts: seq<seq<int>> := [];
    var data_parts: seq<seq<int>> := [];
    var ui, ui_indptr := NumpyUniqueReturnIndex(i);
    // ui_indptr can be proven increasing given the ordering precondition
    assert i[0] in i;
    SeqSetEqualityImpliesEquivalence(i, ui, i[0]);
    assert |ui| > 0;
    if ui_indptr[0] > 0
    {
        assert i[ui_indptr[0]] == 0;
        assert i[0] != i[ui_indptr[0]];
        assert i[0] < i[ui_indptr[0]];
        assert false;
    }
    forall x | x in ui
        ensures 0 <= x < matrix.nrows
    {
        SeqSetEqualityImpliesEquivalence(ui, i, x);
    }

    ui_indptr := ui_indptr + [|j|];
    var new_nnzs := NpDiff(ui_indptr);
    var prev := 0;

    // This variable is declared in lines 1016-1020 of the source code, but
    // we have hoisted the declaration upward because its analogous values are
    // relevant when discussing the invariants of the main loop.
    // We skip declaring the indptr_diff variable in favor of using nnzs[1:] directly.
    var nnzs := [0] + NpDiff(matrix.indptr);
    // Variable representing the value of np.cumsum(nnzs, out=nnzs), which will become the indptr of the resulting matrix.
    var new_indptr := [0];

    // The loop inserts the new indices before the old indices.
    var new_indptr_sep: seq<int> := [];

    // Variables representing the value of np.concatenate((indices|data)_parts)
    var new_indices: seq<int> := [];
    var new_data: seq<int> := [];
    var loop_break_indptr: seq<int> := [0];

    var c := 0;
    while c < |ui|
        invariant 0 <= c <= |ui|
        invariant |new_nnzs| == |ui|
        invariant (c == 0 && prev == 0 && new_indices == []) || (c > 0 && prev == ui[c-1])
        invariant forall k :: 0 <= k < |ui| ==> 0 <= ui[k] < matrix.nrows

        invariant new_indices == NpConcatenate(indices_parts)
        invariant new_data == NpConcatenate(data_parts)
        invariant |new_indptr| == prev + 1 == |new_indptr_sep| + 1
        invariant new_indptr[0] == 0
        invariant forall k :: 0 <= k < |new_indptr| ==> 0 <= new_indptr[k] <= |new_indices|
        invariant forall k :: 0 <= k < |new_indptr|-1 ==> new_indptr[k] <= new_indptr_sep[k] <= |new_indices|
        invariant forall k, l :: 0 <= k < l < |new_indptr| ==> new_indptr[k] <= new_indptr[l]
        invariant forall k :: 0 <= k < |new_indices| ==> 0 <= new_indices[k] < matrix.ncols

        invariant forall x :: 0 <= x < prev ==> new_indptr[x] <= new_indptr_sep[x] <= |new_indices|
        
        invariant forall x, y :: 0 <= x < prev && 0 <= y < matrix.ncols ==> 
            (XYInInput(i, j, x, y) <==> y in new_indices[new_indptr[x]..new_indptr_sep[x]])
        invariant c == 0 || forall y :: 0 <= y < matrix.ncols ==> 
            (XYInInput(i, j, prev, y) <==> y in new_indices[new_indptr[prev]..])
    {
        var ii, js, je := ui[c], ui_indptr[c], ui_indptr[c+1];
        var prev_indices := new_indices;
        // old entries
        var start := matrix.indptr[prev];
        var stop := matrix.indptr[ii];
        indices_parts := indices_parts + [matrix.indices[start..stop]];
        new_indices := new_indices + matrix.indices[start..stop];
        data_parts := data_parts + [matrix.data[start..stop]];
        new_data := new_data + matrix.data[start..stop];

        assert forall x, y :: 0 <= x < prev && 0 <= y < matrix.ncols ==> 
            (XYInInput(i, j, x, y) <==> y in prev_indices[new_indptr[x]..new_indptr_sep[x]]);
        forall x, y | 0 <= x < prev && 0 <= y < matrix.ncols
            ensures XYInInput(i, j, x, y) <==> y in new_indices[new_indptr[x]..new_indptr_sep[x]]
        {
            ShiftedSubsequenceEquality(new_indices, new_indptr[x], new_indptr_sep[x], prev_indices, 0);
        }
        assert forall x, y :: 0 <= x < prev && 0 <= y < matrix.ncols ==> 
            (XYInInput(i, j, x, y) <==> y in new_indices[new_indptr[x]..new_indptr_sep[x]]);

        // Populate values of new_indptr. Note that existence of c implies at least one value must be added.
        // The first row must be special cased, since it may contain indices inserted from the previous loop iteration
        var old_new_indptr := new_indptr;
        var old_new_indptr_sep := new_indptr_sep;
        new_indptr := new_indptr + [|prev_indices|]; // Added at index (prev + 1)
        new_indptr_sep := new_indptr_sep + [|prev_indices|]; // Added at index (prev)

        var k := prev;
        while k < ii
            invariant prev <= k <= ii
            invariant |new_indptr| == k+2 == |new_indptr_sep| + 1
            invariant new_indptr[0] == 0
            invariant new_indptr[k+1] == matrix.indptr[k] + |prev_indices| - matrix.indptr[prev]
            invariant forall l :: prev < l <= k ==> new_indptr[l] == |prev_indices| + matrix.indptr[l] - matrix.indptr[prev]
            invariant forall l :: 0 <= l < |new_indptr| ==> 0 <= new_indptr[l] <= |new_indices|
            invariant forall l :: 0 <= l < |new_indptr|-1 ==> new_indptr[l] <= new_indptr_sep[l] <= |new_indices|
            invariant forall l :: 0 <= l < |old_new_indptr| ==> new_indptr[l] == old_new_indptr[l];
            invariant forall l :: 0 <= l < |old_new_indptr_sep| ==> new_indptr_sep[l] == old_new_indptr_sep[l];
            invariant forall l, m :: 0 <= l < m < |new_indptr| ==> new_indptr[l] <= new_indptr[m]

            invariant new_indptr[prev] <= |prev_indices|
            invariant new_indptr_sep[prev] == |prev_indices|
            invariant forall l :: prev < l <= k ==> new_indptr[l] == new_indptr_sep[l]

            invariant (c == 0) || forall y :: 0 <= y < matrix.ncols ==> (XYInInput(i, j, prev, y) <==> y in prev_indices[new_indptr[prev]..])
        {
            // Modify last entry and add new entry
            new_indptr := new_indptr[k+1 := new_indptr[k+1] + matrix.indptr[k+1] - matrix.indptr[k]];
            new_indptr := new_indptr + [new_indptr[k+1]];
            new_indptr_sep := new_indptr_sep + [new_indptr_sep[k] + matrix.indptr[k+1] - matrix.indptr[k]];
            if k == prev
            {
                assert new_indptr[k+1] == new_indptr_sep[k+1];
            }
            else
            {
                assert new_indptr[k+1] == new_indptr_sep[k+1];
            }
            k := k + 1;
        }

        // handle duplicate j: keep last setting
        var uj, uj_indptr := NumpyUniqueReturnIndex(j[js..je]);
        indices_parts := indices_parts + [seq(|uj_indptr|, k requires 0 <= k < |uj_indptr| => j[js + uj_indptr[k]])];
        new_indices := new_indices + seq(|uj_indptr|, k requires 0 <= k < |uj_indptr| => j[js + uj_indptr[k]]);
        data_parts := data_parts + [seq(|uj_indptr|, k requires 0 <= k < |uj_indptr| => x[js + uj_indptr[k]])];
        new_data := new_data + seq(|uj_indptr|, k requires 0 <= k < |uj_indptr| => x[js + uj_indptr[k]]);
        new_nnzs := new_nnzs[c := |uj|];

        // add new_nnzs[c] to the last element to represent the added matrix entries
        var added_indices := seq(|uj_indptr|, k requires 0 <= k < |uj_indptr| => j[js + uj_indptr[k]]);
        assert added_indices == uj;

        assert i[js] == ii;
        forall jj | js <= jj < je && i[jj] != ii
            ensures false
        {
            assert i[jj] > ii;
            SeqSetEqualityImpliesExistence(i, ui, i[jj]);
            assert exists c1 :: 0 <= c < |ui| && ui[c1] == i[jj];
            forall c1 | 0 <= c1 < |ui| && ui[c1] == i[jj]
                ensures false
            {
                assert c1 > c;
                assert c1 < c+1; // This is also true if ii is the last index for a different reason.
            }
        }
        assert forall k :: 0 <= k < js ==> i[k] < ii;
        assert forall k :: js <= k < je ==> i[k] == ii;
        assert forall k :: je <= k < |i| ==> i[k] > ii;

        if prev < ii
        {
            assert new_indices == prev_indices + matrix.indices[start..stop] + added_indices;

            forall x, y | prev <= x < ii && 0 <= y < matrix.ncols
                ensures y in new_indices[new_indptr_sep[x]..new_indptr[x+1]] <==> y in matrix.indices[matrix.indptr[x]..matrix.indptr[x+1]]
            {
                var old_slice := new_indices[new_indptr_sep[x]..new_indptr[x+1]];
                var matrix_slice := matrix.indices[matrix.indptr[x]..matrix.indptr[x+1]];
                if x == prev
                {
                    assert new_indptr[prev+1] == |prev_indices| + matrix.indptr[prev+1] - matrix.indptr[prev];
                    ShiftedSubsequenceEquality(matrix.indices, matrix.indptr[prev], matrix.indptr[prev+1], new_indices, |prev_indices| - matrix.indptr[prev]);
                    var temp_slice := new_indices[|prev_indices|..new_indptr[prev+1]];
                    assert new_indices[|prev_indices|..new_indptr[prev+1]] == matrix.indices[matrix.indptr[x]..matrix.indptr[x+1]];
                    assert new_indptr_sep[prev] == |prev_indices|;
                    assert temp_slice == old_slice;
                }

                if prev < x < ii
                {
                    ShiftedSubsequenceEquality(matrix.indices, matrix.indptr[x], matrix.indptr[x+1], new_indices, |prev_indices| - matrix.indptr[prev]);
                    assert new_indices[new_indptr[x]..new_indptr[x+1]] == matrix_slice;
                    var slice := new_indices[new_indptr[x]..new_indptr[x+1]];
                    assert new_indptr_sep[x] == new_indptr[x];
                    assert new_indices[new_indptr_sep[x]..new_indptr[x+1]] == slice;
                }
            }
            forall x, y | 0 <= x < ii && 0 <= y < matrix.ncols
                ensures XYInInput(i, j, x, y) <==> y in new_indices[new_indptr[x]..new_indptr_sep[x]]
            {
                if x < prev
                {
                    // This is a repetition of lines 214-222, but including the former speeds up verification
                    assert XYInInput(i, j, x, y) <==> y in prev_indices[old_new_indptr[x]..old_new_indptr_sep[x]];
                    ShiftedSubsequenceEquality(new_indices, new_indptr[x], new_indptr_sep[x], prev_indices, 0);
                }
                if x == prev
                {
                    assert new_indices[new_indptr[prev]..new_indptr_sep[prev]] == prev_indices[new_indptr[prev]..new_indptr_sep[prev]];
                    assert XYInInput(i, j, x, y) <==> y in new_indices[new_indptr[x]..new_indptr_sep[x]];
                }
                if prev < x < ii
                {
                    assert x !in ui;
                    SeqSetEqualityImpliesEquivalence(ui, i, x);
                    assert x !in i;
                    assert !XYInInput(i, j, x, y);
                    assert new_indptr_sep[x] == new_indptr[x];
                    assert y !in new_indices[new_indptr[x]..new_indptr_sep[x]];
                }
            }
        } 
        else
        {
            assert c == 0;
            assert new_indices == added_indices;
        }
        assert new_indptr[ii] == |prev_indices| + matrix.indptr[ii] - matrix.indptr[prev];
        forall y | 0 <= y < matrix.ncols
            ensures XYInInput(i, j, ii, y) <==> y in new_indices[new_indptr[ii]..]
        {
            assert (XYInInput(i, j, ii, y) <==> y in j[js..je]);
            SeqSetEqualityImpliesEquivalence(j[js..je], uj, y);
            assert (y in j[js..je] <==> y in uj);
            assert added_indices == new_indices[new_indptr[ii]..];
        }
        forall y | y in new_indices[new_indptr[ii]..] && !(0 <= y < matrix.ncols)
            ensures false
        {}
        assert forall k :: |prev_indices| <= k < |new_indices| ==> 0 <= new_indices[k] < matrix.ncols;

        // Discard the last entry, since it'll be overridden anyway
        new_indptr := new_indptr[..|new_indptr|-1];
        new_indptr_sep := new_indptr_sep[..|new_indptr_sep|-1];

        prev := ii;

        c := c + 1;
    }

    // remaining old entries
    var start := matrix.indptr[prev]; // equivalent to self.indptr[ii] in source code
    indices_parts := indices_parts + [matrix.indices[start..]];
    new_indices := new_indices + matrix.indices[start..];
    data_parts := data_parts + [matrix.data[start..]];
    new_data := new_data + matrix.data[start..];

    // update attributes
    
}

