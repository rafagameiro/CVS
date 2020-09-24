/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

©2020 João Costa Seco, Eduardo Geraldo

Students
	António Ferraz nº50110
	Rafael Gameiro nº50677
*/

/*@

  predicate P(unit a, Transaction v; unit b) = v != null &*& TransInv(v,_,_,_) &*& b == unit;

  predicate QueueInv(Queue q, predicate(unit, Transaction;unit) p; int n, int m) = 

        q.array |-> ?a
    &*& q.numelements |-> n
    &*& q.head |-> ?h
    &*& q.tail |-> ?t

    &*& a != null
    &*& (h < t || n == a.length ? 
                ( array_slice_deep(a, 0, h, p, unit,  ?in1, _) 
              &*& array_slice(a, h, t, ?out) 
              &*& array_slice_deep(a, t, a.length, p, unit, ?in2, _)) 
            :
            (
             ( array_slice(a, 0, t, ?out1) 
            &*& array_slice_deep(a, t, h, p, unit, ?in,_) 
            &*& array_slice(a, h, a.length, ?out2)) 
            )
         )
    &*& m == a.length
    &*& 0 <= n &*& n <= a.length
    &*& 0 <= h &*& h < a.length
    &*& 0 <= t &*& t < a.length

    &*& (h == t ? n == 0 || n == a.length : true)
    &*& (h > t  ? n == h - t : true)
    &*& (h < t  ? n == h - t + a.length : true);
    
@*/


class Queue {

  Transaction[] array;
  int numelements;
  int head;
  int tail;

  Queue(int size)
  //@ requires size > 0;
  //@ ensures QueueInv(this, P, 0, size);
  {
    array = new Transaction[size];
    numelements = 0;
    head = 0;
    tail = 0;
  }

  void enqueue(Transaction v) 
  //@ requires QueueInv(this, P, ?n, ?m) &*& n < m &*& v != null &*& TransInv(v,_,_,_);
  //@ ensures QueueInv(this, P, n+1, m);
  {
    //@ array_slice_split(array, head, head+1);
    array[head++] = v;
    //@ array_slice_deep_close(array, head-1, P, unit);
    if( head == array.length ) head = 0;
    numelements++;
  }

  Transaction dequeue() 
  //@ requires QueueInv(this, P, ?n, ?m) &*& n > 0;
  //@ ensures QueueInv(this, P, n-1, m) &*& TransHash(unit, result, _);
  {
    Transaction v = array[tail++];
    if( tail == array.length ) tail = 0;
    numelements--;
    return v;
  }

  boolean isFull() 
  //@ requires QueueInv(this, P, ?n, ?m);
  //@ ensures QueueInv(this, P, n, m) &*& result == (n == m);
  {
    return numelements == array.length;
  }

  boolean isEmpty() 
  //@ requires QueueInv(this, P, ?n, ?m);
  //@ ensures QueueInv(this, P, n, m) &*& result == (n == 0);
  {
    return numelements == 0;
  }
}

