include "csr.dfy"
include "GetSubmatrix.dfy"
include "GetIntXInt.dfy"
include "SetMany.dfy"
include "SetIntXInt.dfy"
include "matrix.dfy"
include "CsrToDense.dfy"

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

    var new_matrix := GetSubmatrix(matrix, 0, 1, 0, 1);
    var expected := new CSRMatrix([1], [0], [0, 1], 1, 1);
    // expected
    // [ 1 ]
    assert |expected.data| == 1;
    assert expected.data[0] == 1;

    print new_matrix.data, "\n";
    print new_matrix.indices, "\n";
    print new_matrix.indptr, "\n";

    var value1 := GetIntXInt(matrix, 0, 0);
    assert indices[indptr[0]..indptr[1]] == [0, 2];
    assert 0 in matrix.indices[matrix.indptr[0]..matrix.indptr[1]];
    assert value1 == 1;

    var value2 := GetIntXInt(matrix, 1, 1);
    assert value2 == 0;

    var value3 := GetIntXInt(matrix, 2, 1);
    assert indices[indptr[2]..indptr[3]] == [0, 1, 2];
    assert 1 in matrix.indices[matrix.indptr[2]..matrix.indptr[3]];
    assert value3 == 5;


    var matrix2 := new CSRMatrix([1, 1, 1], [0, 1, 2], [0, 1, 2, 3], 3, 3);
    // matrix:
    // [ 1  0  0 ]     [ 1  0  2 ] 
    // [ 0  1  0 ] ==> [ 0  3  0 ]
    // [ 0  0  1 ]     [ 3  0  1 ]
    SetIntXInt(matrix2, 0, 2, 2);
    assert JExists(matrix2.indices, matrix2.indptr, 0, 2);
    assert !JExists(matrix2.indices, matrix2.indptr, 2, 0);
    assert DataAt(matrix2.data, matrix2.indices, matrix2.indptr, 0, 0) == {1};
    assert DataAt(matrix2.data, matrix2.indices, matrix2.indptr, 0, 2) == {2};
    assert DataAt(matrix2.data, matrix2.indices, matrix2.indptr, 1, 1) == {1};

    var i, j, x := [1, 2], [1, 0], [3, 3];
    SetMany(matrix2, i, j, x);
    assert JExists(matrix2.indices, matrix2.indptr, 0, 2);
    assert DataAt(matrix2.data, matrix2.indices, matrix2.indptr, 0, 0) == {1};
    assert DataAt(matrix2.data, matrix2.indices, matrix2.indptr, 0, 2) == {2};
    assert DataAt(matrix2.data, matrix2.indices, matrix2.indptr, 1, 1) == {3};
    assert i[1] == 2 && j[1] == 0 && x[1] == 3;
    assert JExists(matrix2.indices, matrix2.indptr, 2, 0);
    assert DataAt(matrix2.data, matrix2.indices, matrix2.indptr, 2, 0) == {3};

    var m_data := [[1, 0, 0], [0, 0, 0], [0, 0, 0]];
    var m_rows := 3;
    var m_cols := 3;
    var m := Matrice(m_data, m_rows, m_cols);

    var m_sum := CsrToDense(m, matrix);
    assert |m_sum.vals| == 3;
    assert |m_sum.vals[0]| == 3;
    assert m_sum.vals[0][0] == 2;
    assert m_sum.vals[0][1] == 0;
    // expected
    // 2 0 2
    // 0 0 3
    // 4 5 6

    var empty_m := Matrice([], 0, 0);
    var empty_csr := new CSRMatrix([], [], [0], 0, 0);

    var empty_sum := CsrToDense(empty_m, empty_csr);
    assert |empty_sum.vals| == 0;
    assert empty_sum.vals == [];
    // expected []
}
