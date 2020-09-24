
//Queue based on a circular buffer.

/*@
	predicate QueueInv(Queue q; int r, int w, int l) = 
		q.buffer |-> ?b
	    &*& q.read |-> r 
	    &*& q.write |-> w 
	    &*& q.capacity |-> ?c 
	    &*& q.len |-> l
	    &*& b != null
    	    &*& c == b.length
	    &*& 0 <= r &*& r <= c 
	    &*& 0 <= w &*& w <= c
	    &*& 0 <= l &*& r <= l &*& w <= l
	    &*& array_slice(b, 0, l, ?elems);
	   
@*/

class Queue {

  private int[] buffer;
  private int capacity;
  private int read;
  private int write;
  private int len;

  //creates a new Queue with capacity max.
  Queue(int max) 
  //@ requires max >= 0;
  //@ ensures QueueInv(this, 0, 0, 0);
  {
    buffer = new int[max];
    read = 0;
    write = 0;
    capacity = max;
    len = 0;
  }

  //places the int v at the end of this Queue
  void enqueue(int v)
  ////@ requires QueueInv(this, ?r, ?w, ?l);
  ////@ ensures QueueInv(this, r, w+1, l);
  {
     
     
     buffer[write++] = v;
     len++;
     
     if(write == capacity)
     	write = 0;
  }

  //retrieves the element at the start of this Queue.
  int dequeue()
  //@ requires QueueInv(this, ?r, ?w, ?l) &*& r < l;
  //@ ensures QueueInv(this, r, w, l-1);
  {
    //@open QueueInv(this, ?s, ?e, ?m);
    if(read < len) {
    	//@ array_slice_split(buffer,s,s+1);
    	int val = this.buffer[read++];
    	len--;
    	if(read == capacity)
    		read = 0;
    	return val;
    }
    return -1;
    
  }
  
  //returns true if this Queue has reached its capacity.
  boolean isFull()
  //@ requires QueueInv(this, ?r, ?w, ?l);
  //@ ensures QueueInv(this, r, w, l);
  {
    return write == capacity-1;
  }
  
  //returns true if this Queue has no elements.
  boolean isEmpty()
  //@ requires QueueInv(this, ?r, ?w, ?l);
  //@ ensures QueueInv(this, r, w, l) &*& result?r==w:r != w;
  {
    return read == write;
  }

}