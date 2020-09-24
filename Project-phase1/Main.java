/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

ï¿½2020 Joï¿½o Costa Seco, Eduardo Geraldo

Students
	António Ferraz nº50110
	Rafael Gameiro nº50677
*/

/* 
   The class of Main. 

   It contains the definition for the predicate that defines the 
   representation invariant for blockchain summary blocks.
   
*/

class Main {

    private static Blockchain chain;

    public static void main(String[] args)
    //@ requires chain |-> ?c &*& [_] System.out |-> ?o &*& o != null;
    //@ ensures true;
    {
	System.out.println("Program starts.");
        chain = new Blockchain();
        
	Transaction[] ts;
	int j,i = 0;
	while(i < 5)
	//@ invariant i >= 0 &*& i <= 5 &*& chain |-> ?ch &*& BlockchainInv(ch) &*& ch != null &*& [_] System.out |-> o &*& o != null;
	{
		ts = new Transaction[Block.MAX_ID];

		j = 0;
		while(j < Block.MAX_ID)
		//@ invariant j >= 0 &*& j <= Block.MAX_ID &*& array_slice(ts, j, ts.length, ?elems) &*& array_slice_deep(ts, 0, j, TransHash, unit,_,_);
		{
			Transaction t = new Transaction(i,i+1,10);
			ts[j] = t;
			//@ array_slice_deep_close(ts, j, TransHash, unit);
			j++;
		}
		//@ assert array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_);
		if(chain.isAvailable())
			chain.addSummaryBlock();
		else
			chain.addBlock(ts);
		i++;
	}
	
    }

}
