class Map {
  ghost var m:map<int, char>;
  var a:array<seq<(int, char)>>;

  function repInv() : bool
    reads a, `a
  {
    a.Length > 0 && uniqueKeys(a)
  }

  function uniqueKeys(a:array<seq<(int, char)>>) : bool
    reads a
  {
      forall i :: 0 <= i < a.Length ==> 
      forall j :: j in a[i] ==> forall k :: k in a[i] ==>
      j != k ==> j.0 != k.0 
  }

  function absInv() : bool
    reads a, `a, `m 
  {
    repInv() && sound()
  }

  function sound() : bool
    reads a, `a, `m
    requires repInv()
  {
    forall k :: k in m ==> exists l :: 0 <= l < a.Length && (k, m[k]) in a[l]
  }

 
  function method getHash(key : int) : int
    reads this, a
    requires repInv()
    ensures repInv()
  {
    key % a.Length
  }

  function hasKey(k: int) : bool
    reads this, a
  {
    exists x :: (0 <= x < a.Length ==> exists j :: j in a[x] && j.0 == k)
  }

  constructor ()
    ensures absInv() 
  {
    var size := 20;
    var init:seq<(int, char)> := [];
    a := new seq[size](_=> init);
    m := map[];
  }


  method get(k:int, def:char) returns(v:char)
    requires repInv()
    ensures repInv()
    ensures v != def ==> hasKey(k)
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
    requires repInv()
    ensures repInv()
    ensures z ==> hasKey(k)
    ensures !z ==> forall j :: j in a[getHash(k)] ==> j.0 != k
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
    requires repInv()
    ensures repInv()
    modifies this, a
  {
    var f:bool := this.contains(k);
    if( !f )
    {
      var pos:int := getHash(k);
      a[pos] := a[pos] + [(k, v)];
      m := m[k := v];
      assert forall j :: j in old(a[pos]) ==> j.0 != k;
      assert a[pos] == old(a[pos]) + [(k, v)];
      assert uniqueKeys(a);
    }
  }
  
}