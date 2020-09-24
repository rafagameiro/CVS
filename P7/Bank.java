/*
Starting point for exercise of Lab Session 7.
CVS course - Integrated Master in Computer Science and Engineering
@FCT UNL Luis Caires 2015
*/


class Bank {

    BankAccount store[];
    int nelems;
    int capacity;
    
    /*@
    	predicate BankInv(int n) =
    		this.store |-> ?a
    	    &*& this.nelems |-> n
    	    &*& this.capacity |-> ? m
    	    &*& m == a.length
    	    &*& 0 <= n &*& n <= a.length
    	    &*& array_slice(a, 0, n, ?others);
    @*/

    /*
     * Constructor. Given a size as parameter, initializes the underlying array.
     */
    public Bank(int size) 
    //@ requires size > 0;
    //@ ensures BankInv(0);
    {
    	store = new BankAccount[size];
    	nelems = 0;
    	capacity = size;
    }

    /*
     * Creates and stroes a new account with the id code.
     */
    void addnewAccount(int code)
    // @ requires BankInv(?n) &*& 0 <= code &*& 1000 >= code;
    // @ensures BankInv(n+1);
    {
    	store[nelems] = new BankAccount(code);
    	nelems++;
    }

    /*
     * This operation returns the balance of the account with id code. If the
     * account with id code does not exist, the method returns -1.
     */
    int getbalance(int code) 
    //@requires BankInv(?n);
    //@ensures BankInv(n);
    {
    	int i = 0;
    	while (i < nelems)
    		
    	{
    	   if(store[i].getcode() == code)
    	   	return store[i].getbalance();
    	}
    	return -1;
    }

    /*
     * Removes the account with the id code from this Bank.
     * This operation retuns a boolean indicating whether or not
     * the account was successfully removed.
     */
    boolean removeAccount(int code) {}

    /*
     * This operation transfers val from the account with the id from to the
     * account with the id to.
     * The return of the oiperation shows whether or not the transaction
     * processed successfully.
     */
    boolean transfer(int from, int to, int val) {} 

    /*
     * Operation responisble for the expansion of the array in oreder to
     * accommodate a greater number of accounts.
     */
    void extendstore() {}

}
