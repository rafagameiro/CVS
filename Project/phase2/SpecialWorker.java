/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

©2020 João Costa Seco, Eduardo Geraldo

Students
	António Ferraz nº50110
	Rafael Gameiro nº50677
*/

/*@
	predicate specialWorkerInv(SpecialWorker sw;) =
		    sw.chain |-> ?c
		&*& c != null
		&*& [_]CBlockchainInv(c)
		&*& sw.queue |-> ?q
		&*& q != null
		&*& [_]CQueueInv(q)
		&*& sw.random |-> ?r
		&*& r >= 0;

@*/

/* 
   The class of Worker. 

   It specializes in generating summary blocks only when necessary.
   
*/

class SpecialWorker implements Runnable{

    private CBlockchain chain;
    private TransactionQueue queue;
    private int random;

    //@ predicate pre() = specialWorkerInv(this) &*& [_] System.out |-> ?o &*& o != null;
    //@ predicate post() = true;
    public SpecialWorker(CBlockchain chain, TransactionQueue queue)
    //@ requires chain != null &*& blockchain_frac(?fc) &*& [fc]CBlockchainInv(chain) &*& queue != null &*& queue_frac(?f) &*& [f]CQueueInv(queue) &*& [_] System.out |-> ?o &*& o != null;
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
    	
	while(true)
	//@ invariant specialWorkerInv(this) &*& [_] System.out |-> ?o &*& o != null;
	{
		createSummaryBlock();
	}

    }
    
    private void createSummaryBlock()
    //@ requires specialWorkerInv(this) &*& [_] System.out |-> ?o &*& o != null;
    //@ ensures specialWorkerInv(this) &*& [_] System.out |-> o &*& o != null;
    {
	int random = 0;
        while (!chain.addSummaryBlock(random))
        //@ invariant random >= 0 &*& specialWorkerInv(this) &*& [_] System.out |-> o &*& o != null;
        {
           random++;
        }
    }
}
