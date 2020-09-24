/*
Starting point for exercise of Lab Session 6.
CVS course - Integrated Master in Computer Science and Engineering
@FCT UNL Eduardo Geraldo, João Costa Seco 2019
*/

/*@
	predicate Positive(unit a, int v; unit c) = v >= 0 &*& c == unit;
	
	predicate noteq(int elem, int v; unit c) = v >= 0 &*& elem != v &*& c == unit;
	
	predicate NotEq(Bag a, int elem, int idx;) =
    	       a.array |-> ?b
    	   &*& a.nelems |-> ?n
    	   &*& a != null
    	   &*& 0 <= n &*& n <=b.length
    	   &*& array_slice_deep(b, 0, idx, noteq, elem, _, _)
    	   &*& array_slice_deep(b, idx, n, Positive, unit, _, _)
    	   &*& array_slice(b, n, b.length, _);
@*/

class Bag {

    int[] array;
    int nelems;
    
    /*@
    	predicate BagInv(int n, int m) = 
    	   this.array |-> ?a 
    	   &*& this.nelems |-> n
    	   &*& a != null
    	   &*& m == a.length
    	   &*& 0 <= n &*& n <= a.length
    	   &*& array_slice_deep(a, 0, n, Positive, unit, ?elems,_)
    	   &*& array_slice(a, n, m, ?others);
    	   
    @*/

    /*
     * Initializaes the underlying qarray with the length size.
     */
    public Bag(int size)
    //@ requires size > 0;
    //@ ensures BagInv(0, size);
    {
    	array = new int[size];
    	nelems = 0;
    }
    
    public int get(int i)
    //@ requires BagInv(?n,_) &*& 0 <= i &*& i < n;
    //@ ensures BagInv(n,_);
    {
    	return array[i];
    }

    /*
     * Inserts the integer v into this bag.
     */
    public void insert(int v) 
    //@ requires BagInv(?n, ?m) &*& n < m &*& v >= 0;
    //@ ensures BagInv(n+1, m); 
    {	
    	this.array[nelems] = v;
   	nelems++;
   	// No need to use this ones, Verifast already verifies this
   	// @ array_slice_deep_close(array, n, Positive, unit);
   	// @ array_slice_deep_join(array, 0);
    }

    /*
     * Returns the index of the first occurrence of f in this bag. If the value
     * v is not in this bag, this operation returns -1.
     */
    public int indexOf(int elem) 
    //@ requires BagInv(_,_);
    //@ ensures BagInv(_,_);
    {
    	int i = 0;
    	
    	//@ close NotEq(this, i, elem,_,_);
    	while (i < nelems)
    	//@ invariant array_slice_deep(array, 0, i, noteq, elem, _, _);
    	{
    	   if(array[i] == elem)
    	   	return i;
    	   i++;
    	}
    	return -1;
    }

    /*
     * Removes the element at index idx from this bag.
     */
    public void remove(int idx) 
    ////@ requires BagInv(?n) &*& 0 <= idx &*& idx < n;
    ////@ ensures 
    {
    	
    }

}
