/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

ï¿½2020 Joï¿½o Costa Seco, Eduardo Geraldo

Students
	António Ferraz nº50110
	Rafael Gameiro nº50677
*/

/* These are the predicates defining representation invariants for the blockchain blocks and transactions. */
			
/*@	
	predicate isBlockchain(Blockchain b;) = b == null ? emp : b.head |-> ?l &*& isBlock(l,_);
	
	predicate BlockchainInv(Blockchain b;) =
		    b == null ? emp : b.head |-> ?h
		&*& isBlock(h,_)
		&*& b.size |-> ?s
		&*& s >= 0;
 
	predicate isBlock(Block b;int h) = b == null ? h == 0 : b.BlockInv(_, _, h);

	predicate TransHash(unit a, Transaction t; int hash) =
		    t != null
		&*& TransInv(t, ?s, ?r, ?v)
		&*& hash == tansactionHash(s,r,v);
		
	predicate PosBalance(unit a, int v; unit n) =
			v >= 0 &*& n == unit;
		
	fixpoint boolean ValidID(int id) {
		return 0 <= id && id < Block.MAX_ID;
	}

@*/

/* 
   This class should be implemented in the course of the project 
   development with the expected operations to add and inspect the 
   blocks 
*/

class Blockchain {

	private static final int MAX_USERS = Block.MAX_ID;
	
	private Block head;
	private int size;
	
	public Blockchain() 
	//@ requires true;
	//@ ensures BlockchainInv(this);
	{
	   head = null;
	   size = 0;
	}
	
	public boolean isAvailable()
	//@ requires BlockchainInv(this);
	//@ ensures BlockchainInv(this);
	{
		return size % 10 == 0;
	}
	
	public void addBlock(Transaction[] ts)
	//@ requires BlockchainInv(this) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_) &*& [_] System.out |-> ?o &*& o != null;
	//@ ensures BlockchainInv(this);
	{
		System.out.println("Trying to generate a Simple Block.");
		Block b;
		int r = 0;
		
		if(verifyTransactions(ts)) {
			System.out.println("Failed to create Simple Block!");
			return;
		}
		
		while(true)
		//@ invariant BlockchainInv(this) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_) &*& r >= 0 &*& [_] System.out |-> o &*& o != null;
		{
			
			if(verifySimpleBlock(ts, r)) {
				b = new SimpleBlock(head, r, ts);
				head = b;
				size++;
				System.out.println("Simple Block " + Integer.toString(size) + "generated.");
				break;
			} else {
				r++;
			}
		}
	}
	
	public void addSummaryBlock()
	//@ requires BlockchainInv(this) &*& [_] System.out |-> ?o &*& o != null;
	//@ ensures BlockchainInv(this);
	{
		System.out.println("Generating Summary Block.");
		int r = 0;
		int[] users = getBalances();
		
		while(true)
		//@ invariant BlockchainInv(this) &*& array_slice(users, 0, users.length,?elems) &*& r >= 0 &*& [_] System.out |-> o &*& o != null;
		{	
			if(verifySummaryBlock(users, r)) {
				//@ close ValidCheckpoint(users);
				Block b = new SummaryBlock(head, r, users);
				head = b;
				System.out.println("Summary Block " + Integer.toString(size) + "generated.");
				size++;
				break;
			} else {
				r++;
			}
		}
	}
		
	private int[] getBalances()
	//@ requires BlockchainInv(this);
	//@ ensures BlockchainInv(this) &*& array_slice(result, 0, result.length,?elems) &*& result.length == MAX_USERS; 
	{
		int[] users = new int[MAX_USERS];
		
		int i = 0;
		while(i < MAX_USERS)
		//@ invariant i >= 0 &*& i <= MAX_USERS &*& BlockchainInv(this) &*& array_slice(users, 0, MAX_USERS,?elems);
		{
			users[i] = head == null ? 100 : head.balanceOf(i);
			i++;
		}
		return users;
	}
	
	private boolean verifyTransactions(Transaction[] ts)
	//@ requires BlockchainInv(this) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_);
	//@ ensures BlockchainInv(this) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_);
	{
		int i = 0;
		while(i < ts.length)
		//@invariant i >= 0 &*& i <= ts.length &*& BlockchainInv(this) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_);
		{
			Transaction t = ts[i];
			//@ open TransInv(t,_,_,_);
			int balance = head == null? 0 : head.balanceOf(t.getSender());
			if(t.getAmount() > balance)
				return false;
		}
		return true;
	}
	
	private boolean verifySimpleBlock(Transaction[] ts, int r)
	//@ requires BlockchainInv(this) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_) &*& r >= 0;
	//@ ensures BlockchainInv(this) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_);
	{
		int prevHash = head == null ? 0 : head.hash();
		int tsHash = SimpleBlock.hashTransactions(ts);
		int hash = ((tsHash ^ 3) ^ r);
		
		return (hash & 3) == 0;
	}
	
	private boolean verifySummaryBlock(int[] b, int r)
	//@ requires BlockchainInv(this) &*& array_slice(b, 0, b.length, ?elems) &*& r >= 0;
	//@ ensures BlockchainInv(this) &*& array_slice(b, 0, b.length, elems);
	{
		int prevHash = head == null ? 0 : head.hash();
		int bHash = SummaryBlock.hashBalances(b);
		int hash = ((bHash ^ 3) ^ r);
		
		return (hash & 3) == 0;
	}
}
