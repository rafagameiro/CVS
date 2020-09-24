/*
 * For this exercise, you'll have to implement and verify a set of positive
 * integers using an underlying array.
 *
 * As always, you should, for each method, use the strongest post-conditions
 * and the weakest pre-conditions possible.
 * 
 * The set should follow usual restrictions for a set (no repetitions) plus 
 * that all of its elements must be positive.
 * 
 * In the specification and  implementation of the set you should start by
 * defining the representation invariant for each instance of the set, and
 * the abstract invariant. To define the abstract invariant you will need to
 * make use of ghost variables; variables that help to obtain a better
 * specification but do not influence the execution of the code.
 *
 * Regarding the available operations, it is possible to verify if a given
 * element is in the array. This operation receives an int X and return a
 * boolean; true if X is in the set, false otherwise.
 *
 * Another operation available is the addition of an element to the set.
 * Given an int X, this operation adds X to the set and returns nothing.
 */


class PositiveSet {
  ghost var s:set<int>;
  var a:array<int>;
  var size:int;
  
  constructor (size:int)
    requires size > 0
    ensures AbsInv() 
    ensures s == {}
  {
    a := new int[size];
    this.size := 0;
    s := {};
  }

  method find(e:int) returns (z:int)
    requires AbsInv()
    ensures AbsInv()
    ensures z < 0 <==> forall k :: 0 <= k < size ==> a[k] != e
    ensures z >= 0 ==> z < size && a[z] == e  
  {
    var i:int := 0;
    while i < size
      decreases size - i
      invariant 0 <= i <= size
      invariant forall k :: 0 <= k < i ==> a[k] != e
    {
      if a[i] == e
      {
        return i;
      }

      i := i + 1;
    }
    
    return -1;
  }

  method contains(e:int) returns (b:bool)
    requires AbsInv()
    ensures !b <==> forall k :: 0 <= k < size ==> a[k] != e
  {
    var i:int := 0;
    while i < size
      decreases size - i
      invariant 0 <= i <= size
      invariant forall k :: 0 <= k < i ==> a[k] != e
    {
      if a[i] == e
      {
        return true;
      }

      i := i + 1;
    }
    
    return false;
  }

  method add(e:int)
    requires e >= 0 && AbsInv() && hasSpace()
    ensures s == old(s) + {e}
    ensures AbsInv()
    modifies this, a, this`size
  {
    var f: int := this.find(e);
    if( f < 0 )
    {
      a[size] := e;
      s := s + {e};
      size := size + 1;
      assert a[size - 1] == e;
      assert forall i :: (0 <= i < size-1) ==> (a[i] == old(a[i]));
      assert forall x :: (x in s) <==> exists p :: (0 <= p < size && a[p] == x);
    }
  }

  function AbsInv() : bool
    reads this, a
  {
    RepInv() && Sound()
  }

  function Sound() : bool
    reads this, a
    requires RepInv()
  {
    forall x :: x in s <==> exists k :: (0 <= k < size && a[k] == x)
  }

  function RepInv() : bool
    reads this, a
  {
    a.Length > 0 && 0 <= size <= a.Length
    && uniqueElem(a, 0, size) 
  }

  function uniqueElem(a:array<int>, s:int, n:int) : bool
    reads a
    requires 0 <= s <= n <= a.Length  
  {
    forall k :: s <= k < n ==> forall i :: s <= i < n && i != k ==> a[i] != a[k] 
  }

  function hasSpace() : bool
    reads this, a
    requires RepInv()
  {
    size < a.Length
  }
  
}