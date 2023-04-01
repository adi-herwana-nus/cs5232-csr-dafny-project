method np_diff(arr: seq<int>) returns (diff: seq<int>)
    requires |arr| > 0
    ensures |diff| == |arr| - 1
    ensures forall j :: 0 <= j < |diff| ==> diff[j] == arr[j+1] - arr[j]
{
    diff := [];
    var i := 0;
    while i < |arr| - 1
        invariant 0 <= i <= |arr| - 1
        invariant |diff| == i
        invariant forall j :: 0 <= j < i ==> diff[j] == arr[j+1] - arr[j]
    {
        diff := diff + [arr[i+1] - arr[i]];
        i := i + 1;
    }
}

method np_unique_return_index(arr: seq<int>) returns (values: seq<int>, indices: seq<int>)
    ensures |values| == |indices| <= |arr|
    ensures forall j :: 0 <= j < |arr| ==> arr[j] in values
    ensures forall j :: 0 <= j < |indices| ==> 0 <= indices[j] < |arr|
    ensures forall j :: 0 <= j < |indices| ==> arr[indices[j]] == values[j]
    ensures forall j :: 0 <= j < |indices| ==> forall k :: 0 <= k < indices[j] ==> arr[k] != values[j]
    ensures forall j,k :: 0 <= j < k < |indices| ==> indices[j] < indices[k]
{
    values, indices := [], [];
    var i := 0;
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant |values| == |indices| <= i
        invariant forall j :: 0 <= j < i ==> arr[j] in values
        invariant forall j :: 0 <= j < |indices| ==> 0 <= indices[j] < |arr|
        invariant forall j :: 0 <= j < |indices| ==> arr[indices[j]] == values[j]
        invariant forall j :: 0 <= j < |indices| ==> forall k :: 0 <= k < indices[j] ==> arr[k] != values[j]
        invariant forall j :: 0 <= j < |indices| ==> indices[j] < i
        invariant forall j,k :: 0 <= j < k < |indices| ==> indices[j] < indices[k]
    {
        if arr[i] in values
        {
            // nothing to do here
        }
        else
        {
            values := values + [arr[i]];
            indices := indices + [i];
        }

        i := i + 1;
    }
}

class CSRMatrix {
    var data: seq<int>
    var indices: seq<int>
    var indptr: seq<int>
    var width: int
    var height: int

    method insert_many(i: seq<int>, j: seq<int>, x: seq<int>)
        modifies this
        requires |i| == |j| == |x| > 0
        // The source code sorts the inputs such that i is nondecreasing; we simplify by having it as a precondition
        requires forall k :: 0 < k <= |i| - 1 ==> i[k] >= i[k-1]
    {

        // Collate old and new in chunks by major index
        var indices_parts: seq<seq<int>> := [];
        var data_parts: seq<seq<int>> := [];
        var ui, ui_indptr := np_unique_return_index(i);
        ui_indptr := ui_indptr + [|j|, |j|];
        var c := 0;
        while c < |ui|
            invariant 0 <= c <= |ui|
        {
            var ii, js, je := ui[c], ui_indptr[c], ui_indptr[c+1];
            // handle duplicate j: keep last setting
            // The source code checks if |uj| == je - js (i.e. if all the j entries are already unique)
            // but the resulting array is equivalent (this is likely done to improve performance)
            var uj, uj_indptr := np_unique_return_index(j[js..je]);

            c := c + 1;
        }
    }
}
