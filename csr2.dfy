lemma InsertHead<T>(heads: seq<T>, tails: seq<T>)
    ensures forall j :: 0 <= j < |tails| ==> (
        ((heads + tails)[|heads| + j]) == tails[j]
    )
{

}

lemma ShiftRange<T>(heads: seq<T>, tails: seq<T>)
    ensures forall i1, i2 :: |heads| <= i1 <= i2 <= |heads| + |tails| ==> (
        ((heads + tails)[i1..i2]) == tails[i1-|heads|..i2-|heads|]
    )
{

}

predicate Ascending(arr: seq<int>) {
    forall i,j :: 0 <= i < j < |arr| ==> arr[i] < arr[j]
}

predicate ValidCSRIndex(indices: seq<int>, indptr: seq<int>) {
    |indptr| >= 2 &&
    indptr[0] == 0 &&
    indptr[|indptr| - 1] == |indices| &&
    (forall i :: 0 <= i < |indptr| - 1 ==> 0 <= indptr[i] <= |indices|) &&
    (forall i, j :: 0 <= i < j < |indptr| ==> indptr[i] <= indptr[j])
}

predicate Canonical(indices: seq<int>, indptr: seq<int>)
    requires ValidCSRIndex(indices, indptr)
{
    forall row :: 0 <= row < |indptr|-1 ==> Ascending(indices[indptr[row]..indptr[row+1]])
}

lemma CanonicalAlt(indices: seq<int>, indptr: seq<int>)
    requires ValidCSRIndex(indices, indptr)
    ensures Canonical(indices, indptr) <==> (forall row :: 0 <= row < |indptr|-1 ==> 
        forall j, k :: indptr[row] <= j < k < indptr[row+1] ==> indices[j] < indices[k])
{

}

function CSRToIndexRows(indices: seq<int>, indptr: seq<int>): seq<seq<int>>
    requires ValidCSRIndex(indices, indptr)
{
    // https://github.com/dafny-lang/dafny/issues/1119
    seq(|indptr| - 1, row requires 0 <= row < |indptr| - 1 =>
        indices[indptr[row]..indptr[row+1]])
}

function IndexRowsToIndices(indexRows: seq<seq<int>>): seq<int>
    requires |indexRows| >= 1
    requires forall i :: 0 <= i < |indexRows| ==> Ascending(indexRows[i])
{
    if |indexRows| == 1 then indexRows[0] else indexRows[0] + IndexRowsToIndices(indexRows[1..])
}

function IndexRowsToIndptr(indexRows: seq<seq<int>>): seq<int>
    requires |indexRows| >= 1
    requires forall i :: 0 <= i < |indexRows| ==> Ascending(indexRows[i])
{
    if |indexRows| == 1 then [0, |indexRows[0]|] else (
        [0] + seq(|indexRows|, row requires 0 <= row < |indexRows| =>
        |indexRows[0]| + IndexRowsToIndptr(indexRows[1..])[row])
    )
}

lemma IndexRowsToCSRIsBijective(indexRows: seq<seq<int>>)
    requires |indexRows| >= 1
    requires forall i :: 0 <= i < |indexRows| ==> Ascending(indexRows[i])
    ensures ValidCSRIndex(IndexRowsToIndices(indexRows), IndexRowsToIndptr(indexRows))
    ensures CSRToIndexRows(IndexRowsToIndices(indexRows), IndexRowsToIndptr(indexRows)) == indexRows
    ensures Canonical(IndexRowsToIndices(indexRows), IndexRowsToIndptr(indexRows))
{
    if |indexRows| == 1 {
        assert ValidCSRIndex(IndexRowsToIndices(indexRows), IndexRowsToIndptr(indexRows));
        assert Canonical(IndexRowsToIndices(indexRows), IndexRowsToIndptr(indexRows));
        assert CSRToIndexRows(IndexRowsToIndices(indexRows), IndexRowsToIndptr(indexRows))[0] == indexRows[0];
    } else {
        var head: seq<int> := indexRows[0];
        var tail: seq<seq<int>> := indexRows[1..];
        IndexRowsToCSRIsBijective(tail);

        var tail_indices := IndexRowsToIndices(tail);
        var tail_indptr := IndexRowsToIndptr(tail);

        var indices := head + tail_indices;
        var indptr := [0] + seq(|tail_indptr|, row requires 0 <= row < |tail_indptr| =>
        |head|+tail_indptr[row]);

        assert IndexRowsToIndices(indexRows) == indices;
        assert IndexRowsToIndptr(indexRows) == indptr;

        var inverse := CSRToIndexRows(indices, indptr);
        assert inverse[0] == indices[indptr[0]..indptr[1]];
        InsertHead(head, tail_indices);
        ShiftRange(head, tail_indices);

        assert forall i :: 0 <= i < |indptr| - 1 ==> inverse[i] == indices[indptr[i]..indptr[i+1]] == indexRows[i];
    }
}

lemma CSRToIndexRowsIsBijective(indices: seq<int>, indptr: seq<int>)
    requires ValidCSRIndex(indices, indptr)
    requires Canonical(indices, indptr)
    ensures |CSRToIndexRows(indices, indptr)| >= 1
    ensures forall i :: 0 <= i < |CSRToIndexRows(indices, indptr)| ==> Ascending(CSRToIndexRows(indices, indptr)[i])
    ensures IndexRowsToIndices(CSRToIndexRows(indices, indptr)) == indices
    ensures IndexRowsToIndptr(CSRToIndexRows(indices, indptr)) == indptr
{

}

lemma ApplyFunc<U, V, W>(F: (U, V) -> W, A1: U, A2: U, B1: V, B2: V)
    ensures F(A1, B1) == F(A2, B2)
{

}

predicate ValidIndexRow (indexRow: seq<int>, ncols: int) {
    Ascending(indexRow) && forall i :: 0 <= i < |indexRow| ==> 0 <= indexRow[i] < ncols
}

function IndexRowToDenseIndexRow (indexRow: seq<int>, ncols: int, offset: int, ptr: int) : seq<int>
    requires 0 <= ptr <= ncols
    requires ValidIndexRow (indexRow, ncols)
    decreases ncols - ptr
{
    if ptr == ncols then [] else (
        if |indexRow| == 0 || indexRow[0] != ptr then 
            [-1] + IndexRowToDenseIndexRow(indexRow, ncols, offset, ptr+1)
        else
            [offset] + IndexRowToDenseIndexRow(indexRow[1..], ncols, offset+1, ptr+1))
}

function IndexRowsToDenseIndicesRecur (indexRows: seq<seq<int>>, ncols: int, offset: int) : seq<seq<int>>
    requires ncols > 0
    requires |indexRows| >= 1
    requires forall i :: 0 <= i < |indexRows| ==> ValidIndexRow (indexRows[i], ncols)
{
    if |indexRows| == 1 then [IndexRowToDenseIndexRow(indexRows[0], ncols, offset, 0)] else
        [IndexRowToDenseIndexRow(indexRows[0], ncols, offset, 0)] + 
            IndexRowsToDenseIndicesRecur(indexRows[1..], ncols, offset + |indexRows[0]|)
}

function IndexRowsToDenseIndices (indexRows: seq<seq<int>>, ncols: int) : seq<seq<int>>
    requires ncols > 0
    requires |indexRows| >= 1
    requires forall i :: 0 <= i < |indexRows| ==> ValidIndexRow (indexRows[i], ncols)
{
    IndexRowsToDenseIndicesRecur(indexRows, ncols, 0)
}

class CSRMatrix {
    var data: seq<int>
    var indices: seq<int>
    var indptr: seq<int>
    var nrows: int
    var ncols: int

    ghost var index_rows: seq<seq<int>>;

    constructor (data: seq<int>, indices: seq<int>, indptr: seq<int>, nrows: int, ncols: int) 
        requires |data| == |indices|
        requires ValidCSRIndex(indices, indptr)
        requires Canonical(indices, indptr)
        requires |indptr| == nrows + 1
        requires 0 < nrows
        requires 0 < ncols
        requires forall j :: 0 <= j < |indices| ==> indices[j] < ncols
        
        ensures Valid()
    {
        this.data := data;
        this.indices := indices;
        this.indptr := indptr;
        this.nrows := nrows;
        this.ncols := ncols;

        index_rows := CSRToIndexRows(indices, indptr);
        CSRToIndexRowsIsBijective(indices, indptr);
    }

    predicate Valid() 
        reads this
        requires ValidCSRIndex(indices, indptr)
        requires Canonical(indices, indptr)
        requires |index_rows| >= 1
        requires forall i :: 0 <= i < |index_rows| ==> Ascending(index_rows[i])
    {
        IndexRowsToIndices(this.index_rows) == indices &&
        IndexRowsToIndptr(this.index_rows) == indptr
    }
    // Implementation of get_csr_submatrix (scipy/sparse/csr.h, line 1181)
    // The typical numpy-style getter M[x, y] is implemented as a special case of this method
    // (where ir0 = x, ir1 = x+1, ic0 = y, ic1 = y+1).
    // This implies SciPy uses an O(nnz) search algorithm to access matrix entries,
    // even though an O(log(nnz)) algorithm should be possible using binary search.
    // method GetSubmatrix(ir0: int, ir1: int, ic0: int, ic1: int) returns (new_matrix: CSRMatrix)
    //     // requires 0 <= ir0 < ir1 <= nrows
    //     // requires 0 <= ic0 < ic1 <= ncols
    //     // requires |data| == |indices|
    //     // requires |indptr| == nrows + 1
    //     // requires ValidCSRIndex(indices, indptr)

    //     // requires index_mapping.Keys == (set j1: int | 0 <= j1 < |indices|) 
    //     // requires forall j1 :: 0 <= j1 < |indices| ==> |index_mapping[j1]| == 2
    //     // requires forall j1 :: 0 <= j1 < |indices| ==> 0 <= index_mapping[j1][0] < |indptr| - 1
    //     // requires forall j1 :: 0 <= j1 < |indices| ==> indptr[index_mapping[j1][0]] <= j1 < indptr[index_mapping[j1][0]+1]
    //     // requires forall j1 :: 0 <= j1 < |indices| ==> index_mapping[j1][1] == indices[j1]

    //     // Our goal
    //     // get_XY(j) in [ir0, ir1) X [ic0, ic1) IF AND ONLY IF:
    //     //     there exists some j' in new_matrix s.t. new_matrix.index_mapping[j'] == old_matrix.index_mapping[j] - (ir0, ic0)
    // {
    //     var new_n_row := ir1 - ir0;
    //     var new_n_col := ic1 - ic0;
    //     var kk := 0;
    //     // We skip the counting of nnz/allocation steps because our representation is not bound by CXX memory allocation rules

    //     // Assign.
    //     var new_data := [];
    //     var new_indices := [];
    //     var new_indptr := [0];
    //     var i := 0;

        // The predicted new index mapping (we will prove that the actual index mapping generated is equal to this)
    //     ghost var predicted_new_j_to_new_xy : map<int, seq<int>> := map[];

    //     while i < new_n_row
    //         invariant 0 <= i == |new_indptr| - 1 <= new_n_row
    //         invariant kk == |new_indices| == |new_data|
    //         invariant new_indptr[0] == 0
    //         invariant |new_indptr| >= 1
    //         invariant new_indptr[|new_indptr| - 1] == |new_indices|
    //         invariant forall i1 :: 0 <= i1 <= i ==> 0 <= new_indptr[i1] <= |new_indices|
    //         invariant forall i1, j1 :: 0 <= i1 < j1 < |new_indptr| ==> new_indptr[i1] <= new_indptr[j1]

    //         invariant predicted_new_j_to_new_xy.Keys == (set pos: int | 0 <= pos < |new_data|)
    //         invariant Is2DMap(predicted_new_j_to_new_xy)
    //         invariant forall j1 :: 0 <= j1 < |new_indices| ==> 0 <= predicted_new_j_to_new_xy[j1][0] < i
    //         invariant forall j1 :: 0 <= j1 < |new_indices| ==> new_indptr[predicted_new_j_to_new_xy[j1][0]] <= j1 < new_indptr[predicted_new_j_to_new_xy[j1][0]+1]
    //         invariant forall j1 :: 0 <= j1 < |new_indices| ==> predicted_new_j_to_new_xy[j1][1] == new_indices[j1]
    //     {
    //         var row_start := this.indptr[ir0+i];
    //         var row_end   := this.indptr[ir0+i+1];

    //         var jj := row_start;
    //         while jj < row_end
    //             invariant kk == |new_indices| == |new_data|
    //             invariant new_indptr[0] == 0
    //             invariant forall i1 :: 0 <= i1 <= i ==> 0 <= new_indptr[i1] <= |new_indices|

    //             invariant predicted_new_j_to_new_xy.Keys == (set pos: int | 0 <= pos < |new_data|)
    //             invariant Is2DMap(predicted_new_j_to_new_xy)
    //             invariant forall j1 :: 0 <= j1 < |new_indices| ==> 0 <= predicted_new_j_to_new_xy[j1][0] <= i
    //             invariant forall j1 :: 0 <= j1 < |new_indices| ==> 
    //                 (predicted_new_j_to_new_xy[j1][0]  < i && new_indptr[predicted_new_j_to_new_xy[j1][0]] <= j1 < new_indptr[predicted_new_j_to_new_xy[j1][0]+1]) ||
    //                 (predicted_new_j_to_new_xy[j1][0] == i && new_indptr[predicted_new_j_to_new_xy[j1][0]] <= j1 < kk)
    //             invariant forall j1 :: 0 <= j1 < |new_indices| ==> predicted_new_j_to_new_xy[j1][1] == new_indices[j1]
    //         {
    //             ghost var old_x := this.getX(jj);
    //             ghost var old_y := this.getY(jj);
    //             if ((this.indices[jj] >= ic0) && (this.indices[jj] < ic1)) {
    //                 new_indices := new_indices + [this.indices[jj] - ic0];
    //                 new_data := new_data + [this.data[jj]];
    //                 kk := kk + 1;

    //                 assert old_x == i + ir0;
    //                 assert old_y == this.indices[jj];

    //                 assert XYInBounds(old_x, old_y, ir0, ir1, ic0, ic1);
    //                 ghost var new_j, new_x, new_y := |new_data| - 1, i, this.indices[jj] - ic0;

    //                 predicted_new_j_to_new_xy := append_map(predicted_new_j_to_new_xy, new_j, [new_x, new_y]);
    //             }
    //             else
    //             {
    //                 assert XYInBounds(old_x, old_y, ir0, ir1, ic0, ic1) == false;
    //             }
    //             jj := jj + 1;
    //         }
    //         new_indptr := new_indptr + [kk];

    //         i := i + 1;
    //     }

    //     new_matrix := new CSRMatrix(new_data, new_indices, new_indptr, new_n_row, new_n_col);
    //     if new_matrix.CorrectMapping(predicted_new_j_to_new_xy) 
    //     {
    //        // TODO: Prove goal.
    //     }
    //     else 
    //     {
    //         // TODO: Disprove.
    //     }
    // }
}

// Our goal
// get_XY(j) in [ir0, ir1) X [ic0, ic1) IF AND ONLY IF:
//     there exists some j' in new_matrix s.t. new_matrix.index_mapping[j'] == old_matrix.index_mapping[j] - (ir0, ic0)
// method 
// predicate XYInBounds (x: int, y: int, ir0: int, ir1: int, ic0: int, ic1: int)
// {
//     ir0 <= x < ir1 && ic0 <= y < ic1
// }

// predicate TransfersDataCorrectly(old_matrix: CSRMatrix, new_matrix : CSRMatrix, old_j : int, new_j : int, offset_x : int, offset_y : int)
//     reads old_matrix, new_matrix
//     requires 0 <= old_j < |old_matrix.indices|
//     requires ValidCSRIndex(old_matrix.indices, old_matrix.indptr)
//     requires old_matrix.ValidIndexMapping()

//     requires 0 <= new_j < |new_matrix.indices|
//     requires ValidCSRIndex(new_matrix.indices, new_matrix.indptr)
//     requires new_matrix.ValidIndexMapping()
// {
//     new_matrix.index_mapping[new_j][0] == old_matrix.index_mapping[old_j][0] - offset_x && 
//     new_matrix.index_mapping[new_j][1] == old_matrix.index_mapping[old_j][1] - offset_y
// }

// predicate HasTransferredDataCorrectly(old_matrix: CSRMatrix, new_matrix : CSRMatrix, old_j : int, offset_x : int, offset_y : int)
//     reads old_matrix, new_matrix
//     requires 0 <= old_j < |old_matrix.indices|
//     requires ValidCSRIndex(old_matrix.indices, old_matrix.indptr)
//     requires old_matrix.ValidIndexMapping()

//     requires ValidCSRIndex(new_matrix.indices, new_matrix.indptr)
//     requires new_matrix.ValidIndexMapping()
// {
//     exists new_j :: 0 <= new_j < |new_matrix.indices| && TransfersDataCorrectly(old_matrix, new_matrix, old_j, new_j, offset_x, offset_y)
// }


//     requires 0 <= old_j < |old_matrix.indices|
//     requires ValidCSRIndex(old_matrix.indices, old_matrix.indptr)
//     requires old_matrix.ValidIndexMapping()

//     requires 0 <= new_j < |new_matrix.indices|
//     requires ValidCSRIndex(new_matrix.indices, new_matrix.indptr)
//     requires new_matrix.ValidIndexMapping()
// {
//     var old_x := old_matrix.getX(old_j);
//     var old_y := old_matrix.getY(old_j);
//     var new_x := new_matrix.getX(new_j);
//     var new_y := new_matrix.getY(new_j);

//     return new_matrix[old_xy];
// }