
// implementation of function csr_todense, which takes in a CSR matrix and a normal densematrix, outputs the sum of two matrice
// source code: scipy/scipy/sparse/sparsetools/csr.h line 270
// thie function is called by python code add_matrixDense, which get called when a CSR matrix is added to another dense matrix (+)

include "matrix.dfy"
include "csr.dfy"


method CsrToDense(m: Matrix, csr: CSRMatrix) returns (ret: Matrix)
    requires csr.Valid()
    requires isMatrix(m)

    // requires the shape of two input matrices match
    requires m.rows == csr.nrows && m.columns == csr.ncols

    ensures isMatrix(ret)
    ensures csr.Valid()
    ensures ret.rows == m.rows && ret.columns == m.columns
    ensures forall ix :: 0 <= ix < csr.nrows ==> (
                forall jj :: csr.indptr[ix] <= jj < csr.indptr[ix+1] ==> ret.vals[ix][csr.indices[jj]] == m.vals[ix][csr.indices[jj]] + csr.data[jj] &&
                forall jj :: 0 <= jj < csr.ncols && 
                ( forall ii :: csr.indptr[ix] <= ii < csr.indptr[ix+1] ==> jj != csr.indices[ii]) ==> ret.vals[ix][jj] == m.vals[ix][jj]
            )
    {
        var i := 0;
        ghost var originalM := m;
        var ret_data := new seq<int>[csr.nrows];
        
        while i < csr.nrows 
        invariant 0 <= i <= csr.nrows
        invariant m.vals == originalM.vals
        invariant ret_data.Length == csr.nrows
        invariant forall ii :: 0 <= ii < i ==> |ret_data[ii]| == csr.ncols
        invariant forall ix :: 0 <= ix < i ==> (
            forall jj :: csr.indptr[ix] <= jj < csr.indptr[ix+1] ==> ret_data[ix][csr.indices[jj]] == m.vals[ix][csr.indices[jj]] + csr.data[jj] &&
            forall jj :: 0 <= jj < csr.ncols && 
            ( forall ii :: csr.indptr[ix] <= ii < csr.indptr[ix+1] ==> jj != csr.indices[ii]) ==> ret_data[ix][jj] == m.vals[ix][jj]
        )
        {
            var row := AddVals(m.vals[i], i, csr);
            assert row.Length == csr.ncols;
            ret_data[i] := row[..];
            assert |ret_data[i]| == csr.ncols;
            i := i+1;
        }
        var ret_seq_data := ret_data[..];
        ret := Matrice(ret_seq_data, csr.nrows, csr.ncols);
}



method AddVals(from: seq<int>, start: int, csr: CSRMatrix) returns (ret_row: array<int>)
    requires |from| == csr.ncols
    requires |from| >= 0
    requires 0 <= start < csr.nrows
    requires csr.Valid()

    ensures ret_row.Length == |from|

    // main target of verification: ensures that the output row is the sum of the matrix rol and CSR row by making sures that
    // 1. all data with column index that is not in CSR row indices remains the same as the matrix
    // 2. all data with column index that is in CSR row indices equals to the sum of the matrix data and CSR data
    ensures forall jj :: 0 <= jj < |from| && 
            ( forall ii :: csr.indptr[start] <= ii < csr.indptr[start+1] ==> jj != csr.indices[ii]) ==> ret_row[jj] == from[jj]
    ensures forall jj :: csr.indptr[start] <= jj < csr.indptr[start+1] ==> ret_row[csr.indices[jj]] == from[csr.indices[jj]] + csr.data[jj]
    {
        
        ret_row := new int[|from|];
        var i := 0;
        while i < |from|
        invariant 0 <= i <= |from|
        invariant forall ii :: 0 <= ii < i ==> ret_row[ii] == from[ii]
        {
            ret_row[i] := from[i];
            i := i + 1;
        }
        assert ret_row[..] == from;
        assert forall ii :: 0 <= ii < ret_row.Length ==> ret_row[ii] == from[ii];
        assert ret_row.Length == |from| == csr.ncols;


        var j := csr.indptr[start];
        while j < csr.indptr[start+1]
        invariant csr.indptr[start] <= j <= csr.indptr[start+1]
        invariant forall jj :: 0 <= jj < |from| && 
                                    ( forall ii :: csr.indptr[start] <= ii < csr.indptr[start+1] ==> jj != csr.indices[ii]) ==> ret_row[jj] == from[jj]
        invariant forall jj :: j <= jj < csr.indptr[start+1] ==> ret_row[csr.indices[jj]] == from[csr.indices[jj]]
        invariant forall jj :: csr.indptr[start] <= jj < j ==> ret_row[csr.indices[jj]] == from[csr.indices[jj]] + csr.data[jj]
        {
            ret_row[csr.indices[j]] :=  from[csr.indices[j]] + csr.data[j];
            assert ret_row[csr.indices[j]] ==  from[csr.indices[j]] + csr.data[j];
            j := j + 1;
        }
    }