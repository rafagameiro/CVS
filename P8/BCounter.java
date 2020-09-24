
/* Class representing a bounded counter. The value of this counter is restricted 
 by a set limit upon its creation. Once the value of the counter reaches the
 limit, its is no longer possible to call the inc(); The operation inc()
 increases the value of the counter by 1. To reduce the value, the counter
 has the operation dec(). This operation decreases the value of the counter by 1
 until the value reaches 0.
*/
/*@
	predicate BCounterInv(BCounter b; int v, int m) = b.val |-> v &*& b.max |-> m &*& v >= 0 &*& v <= m;

@*/

class BCounter {

  private int val;
  private int max;

  BCounter(int max)
  //@ requires max >= 0;
  //@ ensures BCounterInv(this, 0, max);
  {
    this.val = 0;
    this.max = max;
  }

  void inc()
  //@ requires BCounterInv(this, ?n, ?m) &*& n < m;
  //@ ensures BCounterInv(this, n+1, m);  
  {
    val++;
  }

  void dec()
  //@ requires BCounterInv(this, ?n, ?m) &*& n > 0;
  //@ ensures BCounterInv(this, n-1, m);
  {
    val--;
  }
  
  int get()
  //@ requires BCounterInv(this, ?n, ?m);
  //@ ensures BCounterInv(this, n, m) &*& result >= 0 &*& result <= m;
  {
    return val;
  }

  int getMax()
  //@ requires BCounterInv(this, ?n, ?m);
  //@ ensures BCounterInv(this, n, m) &*& result == m;
  {
    return max;
  }
  
  public static void main(String[] args)
  //@ requires true;
  //@ ensures true;
  {
    int MAX = 10;
    BCounter counter = new BCounter(MAX);
    //@ assert BCounterInv(counter, 0, MAX);
    
  }
}