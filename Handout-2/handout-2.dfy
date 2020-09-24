class Map {
  ghost var m:map<int, char>;
  var a:array<seq<(int, char)>>;

  //Representative State
  function repInv() : bool
    reads a, `a
  {
    a.Length > 0 && uniqueKeys() && correctHash()
  }

  //Proves that each has unique keys
  function uniqueKeys() : bool
    reads a, `a
  {
      forall i :: 0 <= i < a.Length ==> 
      forall j :: j in a[i] ==> forall k :: k in a[i] ==>
      j != k ==> j.0 != k.0 
  }

  //Proves that each element in a set has the correct hash code
  function correctHash() : bool
    reads a, `a
  {
    forall i :: 0 <= i < a.Length ==> 
    forall j :: j in a[i] ==> getHash(j.0) == i 
  }

  //Abstract State
  function absInv() : bool
    reads a, `a, `m 
  {
    repInv() && sound()
  }

  //Proves that every element in the ghost var map is also in the array of sequences 'a'
  function sound() : bool
    reads a, `a, `m
    requires repInv()
  {
    forall k :: k in m ==> exists l :: 0 <= l < a.Length && (k, m[k]) in a[l] &&
    forall j :: 0 <= j < a.Length ==> forall i :: i in a[j] ==> exists x :: (x in m ==> i.0 == x && i.1 == m[x])
  }

  //returns the hash code of an integer
  function method getHash(key : int) : int
    requires a.Length > 0
    reads `a
  {
    key % a.Length
  }

  //Proves that there is an element in some sequence whose key is the same as the value in 'k'
  function hasKey(k: int) : bool
    reads this, a
  {
    exists x :: (0 <= x < a.Length ==> exists j :: j in a[x] && j.0 == k)
  }

  //Proves that there is an element in some sequence whose tuple is formed by the arguments, 'k' and 'v'
  function hasValue(k: int, v: char) : bool
    reads this, a
  {
    exists x :: (0 <= x < a.Length ==> exists j :: j in a[x] && j == (k, v))
  }

  //Proves that in a certain sequence, there is no element whose key value is the same as the value in 'k'
  function keyNotFound(k: int) : bool
    reads this, a
    requires repInv()
    ensures repInv()
  {
    forall j :: j in a[getHash(k)] ==> j.0 != k 
  }

  constructor ()
    ensures absInv() 
  {
    var size := 20;
    var init:seq<(int, char)> := [];
    a := new seq[size](_=> init);
    m := map[];
  }


  //Searches through the array of sequences and if it finds a tuple 
  //whose key is the same as the value 'k', returns the corresponding
  //v value. Otherwise returns the value of 'def'
  method get(k:int, def:char) returns(v:char)
    requires absInv()
    ensures absInv()
    //if the value of 'v' is different than 'def' then there is a tuple
    // whose key is equal to 'k'
    ensures v != def ==> hasKey(k)
    //if the value of 'v' is equal to 'def', or there isn't a tuple
    //whose key is the same as 'k', or the tuple found has the same value
    // as 'def' 
    ensures v == def ==> hasValue(k, def) || keyNotFound(k) 
  {
    var entries:seq<(int, char)> := a[getHash(k)];
    var len:int := |entries|;
    var i:int := 0;

    while i < len
      decreases len - i
      invariant 0 <= i <= len
      invariant forall j :: 0 <= j < i ==> entries[j].0 != k
    {
      if entries[i].0 == k
      {
        return entries[i].1;
      }

      i := i + 1;
    } 

    return def;
  }


   method contains(k:int) returns(z:bool)
    requires absInv()
    ensures absInv()
    //if z is true, there is a tuple whose key is equal to 'k'
    ensures z ==> hasKey(k)
    //if z is false, there is no tuple whose key is equal to 'k'
    ensures !z ==> keyNotFound(k)
  {
    var entries:seq<(int, char)> := a[getHash(k)];
    var len:int := |entries|;
    var i:int := 0;
    
    while i < len
      decreases len - i
      invariant 0 <= i <= len
      invariant forall j :: 0 <= j < i ==> entries[j].0 != k
    {
      if entries[i].0 == k
      {
        return true;
      }

      i := i + 1;
    } 

    return false;
  }
  

   method put(k:int, v:char)
    requires absInv()
    ensures absInv()
    ensures !hasKey(k) ==> m == old(m[k := v])
    ensures hasKey(k) ==> m == old(m)
    modifies a, `a, `m
  {
    var f:bool := this.contains(k);
    // if there isn't a tuple whose key
    //is the same as 'k'
    if( !f )
    {
      //inserts the tuple (k, v) in the respective sequence
      var pos:int := getHash(k);
      a[pos] := a[pos] + [(k, v)];

      //updates the ghost variable
      m := m[k := v];

      //Dafny doesn't seem to notice the update so here are some asserts 
      //to help it understand the update in the ghost var
      assert forall i :: 0 <= i < a.Length ==> forall j :: 0 <= j < |a[i]| ==> a[i][j] != (k, v) ==> a[i][j] == old(a[i][j]);
      assert exists x :: (0 <= x < a.Length ==> exists j :: (j in a[x] ==> j.0 == k && j.1 == v));
      assert forall k :: k in m ==> exists l :: 0 <= l < a.Length && (k, m[k]) in a[l];
      assert forall j :: 0 <= j < a.Length ==> forall i :: i in a[j] ==> i.0 in m;
    }
  }
  
}