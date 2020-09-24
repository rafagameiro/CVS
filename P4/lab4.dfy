/**
 * The method sortedINsertion receives a sorted array a with na alements and
 * inserts e in a positions such that the array remains sorted. 
 * This operation returns the array after the insertion, the new size of the
 * array, and the position at which the new element was inserted.
 */

method sortedInsertion(a:array<int>, na:int, e:int) returns (z:array<int>, nz:int, pos:int)
    requires 0 <= na < a.Length
    requires sorted(a, na)
    ensures 0 <= pos <= na && a[pos] == e
    ensures sorted(a, na + 1)
    ensures forall k :: 0 <= k < pos ==> a[k] == old(a[k])
    ensures forall k :: pos < k < na ==> a[k] == old(a[k-1])
    modifies a
{
    var i := na;
    if na > 0
    { a[na] := a[na-1];}
    while 0 < i && e < a[i-1]
        decreases i
        invariant 0 <= i <= na
        invariant sorted(a, na+1)
        invariant forall k :: i < k < na + 1 ==> e <= a[k]
        invariant forall k :: 0 <= k < i ==> a[k] == old(a[k])
        invariant forall k :: i < k < na ==> a[k] == old(a[k-1])
    {
        a[i] := a[i-1];
        i := i - 1;
    }
    a[i] := e;

    return a, na + 1, i;
}

function sortedRange(a:array<char>, l:int, h:int):bool
    requires 0 <= l <= h <= a.Length
    reads a
{ forall i, j:: (l <= i < j < h) ==> a[i] <= a[j] }

function sorted(a:array<int>, n:int):bool
    requires 0 <= n <= a.Length
    reads a
{ forall i, j:: (0 <= i < j < n) ==> a[i] <= a[j] }

method orderedInsert(a:array<int>, n:int, v:int)
  requires 0 <= n < a.Length
  requires sorted(a, n)
  modifies a 
  ensures sorted(a, n+1)
