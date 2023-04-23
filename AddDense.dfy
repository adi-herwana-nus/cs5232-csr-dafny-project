// // Implementation of _add_dense (scipy/sparse/_compressed.py, line 347),
// // which directly calls csr_todense (verified in CsrToDense.dfy)
// // This is the method called when the Python code uses + to get the sum of CSR matrix x and dense matrix y.

include "matrix.dfy"
include "csr.dfy"
include "CsrToDense.dfy"

method AddDense(csr : CSRMatrix, matrix : Matrix) returns (ret : Matrix)
    requires csr.Valid()
    requires isMatrix(matrix)
    // requires the shape of two input matrices match
    requires matrix.rows == csr.nrows && matrix.columns == csr.ncols

    ensures isMatrix(ret)
    // verifies the values match after addition
    ensures ret.rows == matrix.rows && ret.columns == matrix.columns
    ensures forall ix :: 0 <= ix < csr.nrows ==> (
                forall jj :: csr.indptr[ix] <= jj < csr.indptr[ix+1] ==> ret.vals[ix][csr.indices[jj]] == matrix.vals[ix][csr.indices[jj]] + csr.data[jj] &&
                forall jj :: 0 <= jj < csr.ncols && 
                ( forall ii :: csr.indptr[ix] <= ii < csr.indptr[ix+1] ==> jj != csr.indices[ii]) ==> ret.vals[ix][jj] == matrix.vals[ix][jj]
            )
{
    assert matrix.rows == csr.nrows && matrix.columns == csr.ncols;
    var m, n := csr.nrows, csr.ncols;
    var data, indices, indptr := csr.data, csr.indices, csr.indptr;
    var csr_copied := new CSRMatrix(data, indices, indptr, m, n);
    ret := CsrToDense(matrix, csr_copied);
}