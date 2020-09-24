/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

©2020 João Costa Seco, Eduardo Geraldo

Students
	António Ferraz nº50110
	Rafael Gameiro nº50677
*/

/*@
	predicate workerInv(Worker w;) =
		    w.chain |-> ?c
		&*& c != null
		&*& [_]CBlockchainInv(c)
		&*& w.queue |-> ?q
		&*& q != null
		&*& [_]CQueueInv(q)
		&*& w.random |-> ?r
		&*& r >= 0;

@*/

/* 
   The class of Worker. 

   It specializes in generating simple blocks by extracting
   transactions from the transaction queue.
   
*/

class Worker implements Runnable {

    private static final int BLK_SIZE = 10;

    private CBlockchain chain;
    private TransactionQueue queue;
    private int random;

    //@ predicate pre() = workerInv(this) &*& [_] System.out |-> ?o &*& o != null;
    //@ predicate post() = true;
    public Worker(CBlockchain chain, TransactionQueue queue)
    //@ requires chain != null &*& blockchain_frac(?fc) &*& [fc]CBlockchainInv(chain) &*& queue != null &*& queue_frac(?fq) &*& [fq]CQueueInv(queue)&*& [_] System.out |-> ?o &*& o != null;
    //@ ensures pre();
    {
        this.chain = chain;
        this.queue = queue;
        random = 0;
    }
    
    public void run()
    //@ requires pre(); 
    //@ ensures post();
    {
    	Transaction[] ts;
	int j = 0;
	while(true)
	//@ invariant workerInv(this) &*& [_] System.out |-> ?o &*& o != null;
	{
		ts = new Transaction[Block.MAX_ID];
	
		for(j = 0; j < ts.length; j++)
		//@ invariant j >= 0 &*& j <= ts.length &*& workerInv(this) &*& array_slice(ts, j, ts.length, ?elems) &*& array_slice_deep(ts, 0, j, TransHash, unit,_,_);
		{
			Transaction t = queue.dequeue();
			ts[j] = t;
			//@ array_slice_deep_close(ts, j, TransHash, unit);
		}
		createBlock(ts);	
	}

    }
    
     private void createBlock(Transaction[] ts)
    //@ requires workerInv(this) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_) &*& [_] System.out |-> ?o &*& o != null;
    //@ ensures workerInv(this);
    {
    	if(!chain.verifyTransactions(ts))
    		return;
    	
        int random = 0;
        while (!chain.addBlock(ts, random))
        //@ invariant random >= 0 &*& workerInv(this) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_) &*& [_] System.out |-> o &*& o != null;
        {
           random++;
        }
        
    }
    
}
