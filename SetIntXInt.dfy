// Implementation of _set_intXint (scipy/sparse/_compressed.py, line 817)
// Inserts new nonzero values at coordinates specified by each element of sequences (i, j), 
// overwriting it if it already exists.

include "csr.dfy"
include "SetMany.dfy"

method SetIntXInt(matrix: CSRMatrix, i: int, j: int, x: int)
    modifies matrix
    requires matrix.Valid()
    requires 0 <= i < matrix.nrows && 0 <= j < matrix.ncols

    ensures matrix.Valid()
    ensures matrix.nrows == old(matrix.nrows)
    ensures matrix.ncols == old(matrix.ncols)

    ensures JExists(matrix.indices, matrix.indptr, i, j)
    ensures DataAt(matrix.data, matrix.indices, matrix.indptr, i, j) == {x}
    ensures forall x1, y1 :: 0 <= x1 < matrix.nrows && 0 <= y1 < matrix.ncols ==> (
        ((x1 != i || y1 != j) && JExists(old(matrix.indices), old(matrix.indptr), x1, y1) ==> 
            (JExists(matrix.indices, matrix.indptr, x1, y1) && DataAt(matrix.data, matrix.indices, matrix.indptr, x1, y1) ==
                DataAt(old(matrix.data), old(matrix.indices), old(matrix.indptr), x1, y1))) &&
        ((x1 != i || y1 != j) && !JExists(old(matrix.indices), old(matrix.indptr), x1, y1) ==> 
            (!JExists(matrix.indices, matrix.indptr, x1, y1)))
    )
{
    SetMany(matrix, [i], [j], [x]);
    assert DataAt(matrix.data, matrix.indices, matrix.indptr, [i][0], [j][0]) == {[x][0]};
}
