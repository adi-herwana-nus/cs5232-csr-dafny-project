// ghost method append_map<U,V> (old_map: map<U,V>, key: U, value: V) returns (new_map: map<U,V>)
//     requires key in old_map.Keys <==> false
//     ensures new_map.Keys == old_map.Keys + {key}
//     ensures forall k :: k in old_map.Keys ==> new_map[k] == old_map[k]
//     ensures new_map[key] == value
// {
//     new_map := map k | k in old_map.Keys + {key} :: 
//         if k in old_map.Keys then old_map[k] else value;
// }

// ghost method chain_map<U,V,W> (map1: map<U,V>, map2: map<V,W>) returns (map3: map<U,W>)
//     requires map1.Values <= map2.Keys
//     ensures map3.Keys == map1.Keys
//     ensures forall k :: k in map1.Keys ==> map3[k] == map2[map1[k]]
// {
//     map3 := map k | k in map1.Keys :: map2[map1[k]];
// }

function append_map<U,V> (old_map: map<U,V>, key: U, value: V) : map<U,V>
    requires key in old_map.Keys <==> false
{
    map k | k in old_map.Keys + {key} :: 
        if k in old_map.Keys then old_map[k] else value
}

function chain_map<U,V,W> (map1: map<U,V>, map2: map<V,W>) : map<U,W>
    requires map1.Values <= map2.Keys
{
    map k | k in map1.Keys :: map2[map1[k]]
}

predicate Is2DMap (map1: map<int, seq<int>>)
{
    forall j :: j in map1.Keys ==> |map1[j]| == 2
}

lemma Appended2DMapIs2D (map1: map<int,seq<int>>, j: int, x: int, y: int)
    requires Is2DMap(map1)
    ensures Is2DMap(append_map(map1, j, [x, y]))
{

}

lemma Chained2DMapIs2D (map1: map<int,int>, map2: map<int,seq<int>>)
    requires Is2DMap(map2)
    ensures Is2DMap(chain_map(map1, map2))
{

}

predicate maps_2d_equal_with_offset (map1: map<int, seq<int>>, map2: map<int, seq<int>>, x_offset: int, y_offset: int)
{
    map1.Keys == map2.Keys &&
    Is2DMap(map1) &&
    Is2DMap(map2) &&
    forall j :: j in map1.Keys ==> 
        map2[j][0] == map1[j][0] + x_offset &&
        map2[j][1] == map1[j][1] + y_offset
}

lemma OffsetPreservedOnAppend (map1: map<int,seq<int>>, map2: map<int,seq<int>>, j: int, x1: int, y1: int, x2: int, y2: int, x_offset: int, y_offset: int)
    requires x2 == x1 + x_offset
    requires y2 == y1 + y_offset
    requires maps_2d_equal_with_offset(map1, map2, x_offset, y_offset)
    ensures maps_2d_equal_with_offset(append_map(map1, j, [x1, y1]), append_map(map2, j, [x2, y2]), x_offset, y_offset)
{

}

predicate ValidIndexPtrs(indices: seq<int>, indptr: seq<int>) {
    |indptr| >= 2 &&
    indptr[0] == 0 &&
    indptr[|indptr| - 1] == |indices| &&
    forall i :: 0 <= i < |indptr| - 1 ==> 0 <= indptr[i] <= |indices| &&
    forall i, j :: 0 <= i < j < |indptr| ==> indptr[i] <= indptr[j]
}

predicate Canonical(indices: seq<int>, indptr: seq<int>)
    requires ValidIndexPtrs(indices, indptr)
{
    forall i :: 0 <= i < |indptr|-1 ==> forall j, k :: indptr[i] <= j < k < indptr[i+1] ==> indices[j] < indices[k]
}




class CSRMatrix {
    var data: seq<int>
    var indices: seq<int>
    var indptr: seq<int>
    var nrows: int
    var ncols: int

    ghost var index_mapping: map<int, seq<int>>;

    constructor (data: seq<int>, indices: seq<int>, indptr: seq<int>, nrows: int, ncols: int) 
        requires |data| == |indices|
        requires ValidIndexPtrs(indices, indptr)
        requires |indptr| == nrows + 1
        requires 0 <= nrows
        requires 0 <= ncols
        
        ensures ValidIndexMapping()
    {
        this.data := data;
        this.indices := indices;
        this.indptr := indptr;
        this.nrows := nrows;
        this.ncols := ncols;

        var j := 0;
        var x := 0;
        ghost var ghost_im : map<int, seq<int>> := map[];

        while j < |indices|
            invariant 0 <= j <= |indices|
            invariant 0 <= x < |indptr| - 1
            invariant indptr[x] <= j
            invariant ghost_im.Keys == (set j1: int | 0 <= j1 < j) 
            invariant forall j1 :: 0 <= j1 < j ==> |ghost_im[j1]| == 2
            invariant forall j1 :: 0 <= j1 < j ==> 0 <= ghost_im[j1][0] < |indptr| - 1
            invariant forall j1 :: 0 <= j1 < j ==> indptr[ghost_im[j1][0]] <= j1 < indptr[ghost_im[j1][0]+1]
            invariant forall j1 :: 0 <= j1 < j ==> ghost_im[j1][1] == indices[j1]
        {
            while x < |indptr| - 1 && indptr[x+1] <= j
                invariant 0 <= x < |indptr| - 1
                invariant indptr[x] <= j
            {
                x := x + 1;
            }

            var y := indices[j];
            ghost_im := append_map(ghost_im, j, [x, y]);

            j := j + 1;
        }

        this.index_mapping := ghost_im;
    }

    predicate ValidIndexMapping()
        reads this
    {
        index_mapping.Keys == (set j1: int | 0 <= j1 < |indices|) &&
        Is2DMap(index_mapping) &&
        (forall j1 :: 0 <= j1 < |indices| ==> 0 <= index_mapping[j1][0] < |indptr| - 1) &&
        (forall j1 :: 0 <= j1 < |indices| ==> indptr[index_mapping[j1][0]] <= j1 < indptr[index_mapping[j1][0]+1]) && (forall j1 :: 0 <= j1 < |indices| ==> index_mapping[j1][1] == indices[j1])
    }

    method getX(j: int) returns (x: int)
        requires 0 <= j < |indices|
        requires ValidIndexPtrs(indices, indptr)
        requires ValidIndexMapping()

        ensures 0 <= x < |indptr| - 1
        ensures indptr[x] <= j < indptr[x+1]
        ensures x == index_mapping[j][0]
    {
        x := 0;
        // the first assertion should be unnecessary: this is guaranteed to terminate at the last entry
        while x < |indptr| - 1 && indptr[x+1] <= j
            invariant 0 <= x < |indptr| - 1
            invariant indptr[x] <= j
        {
            x := x+1;
        }
        // It seems like Dafny is already aware of this, even when removing the first while loop condition fails to verify
        assert x < |indptr| - 1;
    }

    method getY(j: int) returns (y: int)
        requires 0 <= j < |indices|
        requires ValidIndexMapping()

        ensures y == index_mapping[j][1]
    {
        y := indices[j];
    }

    predicate CorrectMapping(index_mapping2: map<int, seq<int>>)
        reads this
        requires ValidIndexMapping()
    {
        index_mapping2.Keys == (set j1: int | 0 <= j1 < |indices|) &&
        Is2DMap(index_mapping2) &&
        (forall j1 :: 0 <= j1 < |indices| ==> index_mapping2[j1] == index_mapping[j1])
    }

    // Implementation of get_csr_submatrix (scipy/sparse/csr.h, line 1181)
    // The typical numpy-style getter M[x, y] is implemented as a special case of this method
    // (where ir0 = x, ir1 = x+1, ic0 = y, ic1 = y+1).
    // This implies SciPy uses an O(nnz) search algorithm to access matrix entries,
    // even though an O(log(nnz)) algorithm should be possible using binary search.
    method GetSubmatrix(ir0: int, ir1: int, ic0: int, ic1: int) returns (new_matrix: CSRMatrix)
        requires 0 <= ir0 < ir1 <= nrows
        requires 0 <= ic0 < ic1 <= ncols
        requires |data| == |indices|
        requires |indptr| == nrows + 1
        requires ValidIndexPtrs(indices, indptr)

        requires index_mapping.Keys == (set j1: int | 0 <= j1 < |indices|) 
        requires forall j1 :: 0 <= j1 < |indices| ==> |index_mapping[j1]| == 2
        requires forall j1 :: 0 <= j1 < |indices| ==> 0 <= index_mapping[j1][0] < |indptr| - 1
        requires forall j1 :: 0 <= j1 < |indices| ==> indptr[index_mapping[j1][0]] <= j1 < indptr[index_mapping[j1][0]+1]
        requires forall j1 :: 0 <= j1 < |indices| ==> index_mapping[j1][1] == indices[j1]

        // Our goal
        // get_XY(j) in [ir0, ir1) X [ic0, ic1) IF AND ONLY IF:
        //     there exists some j' in new_matrix s.t. new_matrix.index_mapping[j'] == old_matrix.index_mapping[j] - (ir0, ic0)
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

        // The predicted new index mapping (we will prove that the actual index mapping generated is equal to this)
        ghost var predicted_new_j_to_new_xy : map<int, seq<int>> := map[];

        while i < new_n_row
            invariant 0 <= i == |new_indptr| - 1 <= new_n_row
            invariant kk == |new_indices| == |new_data|
            invariant new_indptr[0] == 0
            invariant |new_indptr| >= 1
            invariant new_indptr[|new_indptr| - 1] == |new_indices|
            invariant forall i1 :: 0 <= i1 <= i ==> 0 <= new_indptr[i1] <= |new_indices|
            invariant forall i1, j1 :: 0 <= i1 < j1 < |new_indptr| ==> new_indptr[i1] <= new_indptr[j1]

            invariant predicted_new_j_to_new_xy.Keys == (set pos: int | 0 <= pos < |new_data|)
            invariant Is2DMap(predicted_new_j_to_new_xy)
            invariant forall j1 :: 0 <= j1 < |new_indices| ==> 0 <= predicted_new_j_to_new_xy[j1][0] < i
            invariant forall j1 :: 0 <= j1 < |new_indices| ==> new_indptr[predicted_new_j_to_new_xy[j1][0]] <= j1 < new_indptr[predicted_new_j_to_new_xy[j1][0]+1]
            invariant forall j1 :: 0 <= j1 < |new_indices| ==> predicted_new_j_to_new_xy[j1][1] == new_indices[j1]
        {
            var row_start := this.indptr[ir0+i];
            var row_end   := this.indptr[ir0+i+1];

            var jj := row_start;
            while jj < row_end
                invariant kk == |new_indices| == |new_data|
                invariant new_indptr[0] == 0
                invariant forall i1 :: 0 <= i1 <= i ==> 0 <= new_indptr[i1] <= |new_indices|

                invariant predicted_new_j_to_new_xy.Keys == (set pos: int | 0 <= pos < |new_data|)
                invariant Is2DMap(predicted_new_j_to_new_xy)
                invariant forall j1 :: 0 <= j1 < |new_indices| ==> 0 <= predicted_new_j_to_new_xy[j1][0] <= i
                invariant forall j1 :: 0 <= j1 < |new_indices| ==> 
                    (predicted_new_j_to_new_xy[j1][0]  < i && new_indptr[predicted_new_j_to_new_xy[j1][0]] <= j1 < new_indptr[predicted_new_j_to_new_xy[j1][0]+1]) ||
                    (predicted_new_j_to_new_xy[j1][0] == i && new_indptr[predicted_new_j_to_new_xy[j1][0]] <= j1 < kk)
                invariant forall j1 :: 0 <= j1 < |new_indices| ==> predicted_new_j_to_new_xy[j1][1] == new_indices[j1]
            {
                ghost var old_x := this.getX(jj);
                ghost var old_y := this.getY(jj);
                if ((this.indices[jj] >= ic0) && (this.indices[jj] < ic1)) {
                    new_indices := new_indices + [this.indices[jj] - ic0];
                    new_data := new_data + [this.data[jj]];
                    kk := kk + 1;

                    assert old_x == i + ir0;
                    assert old_y == this.indices[jj];

                    assert XYInBounds(old_x, old_y, ir0, ir1, ic0, ic1);
                    ghost var new_j, new_x, new_y := |new_data| - 1, i, this.indices[jj] - ic0;

                    predicted_new_j_to_new_xy := append_map(predicted_new_j_to_new_xy, new_j, [new_x, new_y]);
                }
                else
                {
                    assert XYInBounds(old_x, old_y, ir0, ir1, ic0, ic1) == false;
                }
                jj := jj + 1;
            }
            new_indptr := new_indptr + [kk];

            i := i + 1;
        }

        new_matrix := new CSRMatrix(new_data, new_indices, new_indptr, new_n_row, new_n_col);
        if new_matrix.CorrectMapping(predicted_new_j_to_new_xy) 
        {
           // TODO: Prove goal.
        }
        else 
        {
            // TODO: Disprove.
        }
    }
}

// Our goal
// get_XY(j) in [ir0, ir1) X [ic0, ic1) IF AND ONLY IF:
//     there exists some j' in new_matrix s.t. new_matrix.index_mapping[j'] == old_matrix.index_mapping[j] - (ir0, ic0)
// method 
predicate XYInBounds (x: int, y: int, ir0: int, ir1: int, ic0: int, ic1: int)
{
    ir0 <= x < ir1 && ic0 <= y < ic1
}

predicate TransfersDataCorrectly(old_matrix: CSRMatrix, new_matrix : CSRMatrix, old_j : int, new_j : int, offset_x : int, offset_y : int)
    reads old_matrix, new_matrix
    requires 0 <= old_j < |old_matrix.indices|
    requires ValidIndexPtrs(old_matrix.indices, old_matrix.indptr)
    requires old_matrix.ValidIndexMapping()

    requires 0 <= new_j < |new_matrix.indices|
    requires ValidIndexPtrs(new_matrix.indices, new_matrix.indptr)
    requires new_matrix.ValidIndexMapping()
{
    new_matrix.index_mapping[new_j][0] == old_matrix.index_mapping[old_j][0] - offset_x && 
    new_matrix.index_mapping[new_j][1] == old_matrix.index_mapping[old_j][1] - offset_y
}

predicate HasTransferredDataCorrectly(old_matrix: CSRMatrix, new_matrix : CSRMatrix, old_j : int, offset_x : int, offset_y : int)
    reads old_matrix, new_matrix
    requires 0 <= old_j < |old_matrix.indices|
    requires ValidIndexPtrs(old_matrix.indices, old_matrix.indptr)
    requires old_matrix.ValidIndexMapping()

    requires ValidIndexPtrs(new_matrix.indices, new_matrix.indptr)
    requires new_matrix.ValidIndexMapping()
{
    exists new_j :: 0 <= new_j < |new_matrix.indices| && TransfersDataCorrectly(old_matrix, new_matrix, old_j, new_j, offset_x, offset_y)
}


//     requires 0 <= old_j < |old_matrix.indices|
//     requires ValidIndexPtrs(old_matrix.indices, old_matrix.indptr)
//     requires old_matrix.ValidIndexMapping()

//     requires 0 <= new_j < |new_matrix.indices|
//     requires ValidIndexPtrs(new_matrix.indices, new_matrix.indptr)
//     requires new_matrix.ValidIndexMapping()
// {
//     var old_x := old_matrix.getX(old_j);
//     var old_y := old_matrix.getY(old_j);
//     var new_x := new_matrix.getX(new_j);
//     var new_y := new_matrix.getY(new_j);

//     return new_matrix[old_xy];
// }
