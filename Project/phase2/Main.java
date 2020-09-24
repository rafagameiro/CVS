/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

©2020 João Costa Seco, Eduardo Geraldo

Students
	António Ferraz nº50110
	Rafael Gameiro nº50677
*/

/*@
     
      predicate blockchain_frac(real f) = true;

      predicate queue_frac(real f) = true;

@*/

/* 
   The class of Main. 

   It contains the definition for the predicate that defines the 
   representation invariant for blockchain summary blocks.
   
*/

class Main {

    private static final int QUEUE_SIZE = Block.MAX_ID;
    private static final int MAX_WORKERS = 5;

    public static void main(String[] args)
    //@ requires [_] System.out |-> ?o &*& o != null;
    //@ ensures true;
    {
	System.out.println("Program starts.");
        CBlockchain chain = new CBlockchain();
        TransactionQueue queue = new TransactionQueue(QUEUE_SIZE);
        
        //@ close queue_frac(1/3);
        new Thread(new Client(queue)).start();
        
        
        //@ close queue_frac(2/3);
        //@ close blockchain_frac(1/2);
        for(int i = 0; i < MAX_WORKERS; i++)
        //@ invariant queue_frac(?fq) &*& [fq]CQueueInv(queue) &*& blockchain_frac(?fb) &*& [fb]CBlockchainInv(chain) &*& [_] System.out |-> o &*& o != null;
        {
        	//@ open queue_frac(fq);
        	//@ open blockchain_frac(fb);
        	
        	
        	//@ close queue_frac(fq/2);
        	//@ close blockchain_frac(fb/2);
        	new Thread(new SpecialWorker(chain, queue)).start();
		
		//@ close queue_frac(fq/4);
		//@ close blockchain_frac(fb/4);
		new Thread(new Worker(chain, queue)).start();
		
		//@ close queue_frac(fq/4);
		//@ close blockchain_frac(fb/4);
        }
        
	
    }

}
