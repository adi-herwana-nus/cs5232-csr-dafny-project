datatype Matrix = Matrice(vals: seq<seq<int>>, rows: int, columns: int)

predicate isMatrix(mat: Matrix) {
    mat.rows >= 1 && mat.columns >= 1 && |mat.vals| == mat.rows && forall i :: 0 <= i < mat.rows ==> |mat.vals[i]| == mat.columns
}
