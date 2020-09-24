/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

©2020 João Costa Seco, Eduardo Geraldo

Students
	António Ferraz nº50110
	Rafael Gameiro nº50677
*/
			
/*@	
	
	predicate BlockchainInv(Blockchain b, int s;) =
		    b == null ? emp : b.head |-> ?h
		&*& isBlock(h,_)
		&*& b.size |-> s
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

class Blockchain {

	private static final int MAX_USERS = Block.MAX_ID;
	
	private Block head;
	private int size;
	
	public Blockchain() 
	//@ requires true;
	//@ ensures BlockchainInv(this,0);
	{
	   head = null;
	   size = 0;
	}
	
	public boolean isAvailable()
	//@ requires BlockchainInv(this, ?n);
	//@ ensures BlockchainInv(this, n) &*& result? n % 10 == 0: n % 10 > 0;
	{
		return size % 10 == 0;
	}
	
	public boolean addBlock(Transaction[] ts, int random)
	//@ requires BlockchainInv(this, ?n) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_) &*& random >= 0 &*& [_] System.out |-> ?o &*& o != null;
	//@ ensures result?BlockchainInv(this, n+1):array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_) &*& BlockchainInv(this, n);
	{
		System.out.println("Trying to generate a Simple Block.");
		Block b;
			
		if(verifySimpleBlock(ts, random)) {
			b = new SimpleBlock(head, random, ts);
			head = b;
			size++;
			System.out.println("Simple Block " + Integer.toString(size) + "generated.");
			return true;
		} 
		
		System.out.println("Failed to create Simple Block!");
		return false;
	}
	
	public boolean addSummaryBlock(int random)
	//@ requires BlockchainInv(this, ?n) &*& random >= 0 &*& [_] System.out |-> ?o &*& o != null;
	//@ ensures result?BlockchainInv(this, n+1):BlockchainInv(this, n);
	{
		System.out.println("Generating Summary Block.");
		int[] users = getBalances();
		
		if(verifySummaryBlock(users, random)) {
			//@ close ValidCheckpoint(users);
			Block b = new SummaryBlock(head, random, users);
			head = b;
			size++;
			System.out.println("Summary Block " + Integer.toString(size) + "generated.");
			return true;
		}
		return false;
	}
	
	public boolean verifyTransactions(Transaction[] ts)
	//@ requires BlockchainInv(this, ?n) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_);
	//@ ensures BlockchainInv(this, n) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_);
	{
		int[] balances = getBalances();
		
		int i = 0;
		while(i < ts.length)
		//@invariant i >= 0 &*& i <= ts.length &*& BlockchainInv(this, n) &*& array_slice(balances, 0, balances.length,?elems) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_);
		{
			Transaction t = ts[i];
			//@ open TransInv(t,_,_,_);
			int srcIdx = t.getSender();
			int destIdx = t.getReceiver();
			if(t.getAmount() > balances[srcIdx])
				return false;
			else {
				balances[srcIdx] = balances[srcIdx] - t.getAmount();
				balances[destIdx] = balances[destIdx] + t.getAmount();	
			}
		}
		return true;
	}
		
	private int[] getBalances()
	//@ requires BlockchainInv(this, ?n);
	//@ ensures BlockchainInv(this, n) &*& array_slice(result, 0, result.length,?elems) &*& result.length == MAX_USERS; 
	{
		int[] users = new int[MAX_USERS];
		
		int i = 0;
		while(i < MAX_USERS)
		//@ invariant i >= 0 &*& i <= MAX_USERS &*& BlockchainInv(this, n) &*& array_slice(users, 0, MAX_USERS,?elems);
		{
			users[i] = head == null ? 100 : head.balanceOf(i);
			i++;
		}
		return users;
	}
	
	private boolean verifySimpleBlock(Transaction[] ts, int r)
	//@ requires BlockchainInv(this, ?n) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_) &*& r >= 0;
	//@ ensures BlockchainInv(this, n) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_);
	{
		int prevHash = head == null ? 0 : head.hash();
		int tsHash = SimpleBlock.hashTransactions(ts);
		int hash = ((tsHash ^ 3) ^ r);
		
		return (hash & 3) == 0;
	}
	
	private boolean verifySummaryBlock(int[] b, int r)
	//@ requires BlockchainInv(this, ?n) &*& array_slice(b, 0, b.length, ?elems) &*& r >= 0;
	//@ ensures BlockchainInv(this, n) &*& array_slice(b, 0, b.length, elems);
	{
		int prevHash = head == null ? 0 : head.hash();
		int bHash = SummaryBlock.hashBalances(b);
		int hash = ((bHash ^ 3) ^ r);
		
		return (hash & 3) == 0;
	}
}
