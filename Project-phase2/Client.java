/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

©2020 João Costa Seco, Eduardo Geraldo

Students
	António Ferraz nº50110
	Rafael Gameiro nº50677
*/

/*@
	predicate clientInv(Client c;) =
		    c.queue |-> ?q
		&*& q != null
		&*& [_]CQueueInv(q);

@*/

class Client implements Runnable {

    private static final int MAX_VAL = Block.MAX_ID-1;

    private TransactionQueue queue;

    //@ predicate pre() = clientInv(this);
    //@ predicate post() = true;
    public Client(TransactionQueue queue)
    //@ requires queue != null &*& queue_frac(?f) &*& [f]CQueueInv(queue);
    //@ ensures pre();
    {
        this.queue = queue;
    }
    
    public void run()
    //@ requires pre();
    //@ ensures post();
    {
	int i = 0;
	while(true)
	//@ invariant i >= 0 &*& i < MAX_VAL &*& clientInv(this);
	{
		
		Transaction t = new Transaction(i, i + 1, 10);
		queue.enqueue(t);
		i++;
		if(i == MAX_VAL)
			i = 0;
		
	}
    }
}
