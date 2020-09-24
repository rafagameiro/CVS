import java.util.concurrent.locks.*;	

/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

©2020 João Costa Seco, Eduardo Geraldo

Students
	António Ferraz nº50110
	Rafael Gameiro nº50677
*/
	
/*@

    predicate_ctor CBlockchain_shared_state(CBlockchain cbc)() = cbc.chain |-> ?c &*& c != null &*& BlockchainInv(c, ?n) &*& n >= 0;

    predicate_ctor CBlockchain_needsSimple(CBlockchain cbc)() = cbc.chain |-> ?c &*& c != null &*& BlockchainInv(c, ?n) &*& n >= 0 &*& n % 10 > 0;
    
    predicate_ctor CBlockchain_needsSummary(CBlockchain cbc)() = cbc.chain |-> ?c &*& c != null &*& BlockchainInv(c, ?n) &*& n >= 0 &*& n % 10 == 0;

    predicate CBlockchainInv(CBlockchain cbc;) =
            cbc.mon |-> ?l
    	&*& cbc.needsummary |-> ?ce
    	&*& cbc.needsimple |-> ?cf

    	&*& l != null
    	&*& ce != null
    	&*& cf != null

    	&*& lck(l, 1, CBlockchain_shared_state(cbc))
    	&*& cond(ce, CBlockchain_shared_state(cbc), CBlockchain_needsSummary(cbc))
    	&*& cond(cf, CBlockchain_shared_state(cbc), CBlockchain_needsSimple(cbc));

@*/

class CBlockchain {

	Blockchain chain;
	
	ReentrantLock mon;
  	Condition needsimple;
  	Condition needsummary;
	
	public CBlockchain() 
	//@ requires true;
	//@ ensures CBlockchainInv(this);
	{
	   	chain = new Blockchain();
    		//@ close CBlockchain_shared_state(this)();
    		//@ close enter_lck(1, CBlockchain_shared_state(this));
    		mon = new ReentrantLock();
    		//@ close set_cond(CBlockchain_shared_state(this), CBlockchain_needsSummary(this));
    		needsummary = mon.newCondition();
    		//@ close set_cond(CBlockchain_shared_state(this), CBlockchain_needsSimple(this));
    		needsimple = mon.newCondition();
	}
	
	public boolean addBlock(Transaction[] ts, int random)
	//@ requires [_]CBlockchainInv(this) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_) &*& random >= 0 &*& [_] System.out |-> ?o &*& o != null;
  	//@ ensures [_]CBlockchainInv(this) &*& result?true:array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_);
	{
		mon.lock();
    		//@ open CBlockchain_shared_state(this)();
		if( chain.isAvailable() ) {
		    //@ close CBlockchain_shared_state(this)();
		    needsimple.await();
		    //@ open CBlockchain_needsSimple(this)();
		}
		
		boolean result = chain.addBlock(ts, random);
		
		if( chain.isAvailable() ) {
		    //@ close CBlockchain_needsSummary(this)();
		    needsummary.signal();
		    //@ open CBlockchain_shared_state(this)();
		}
		//@ close CBlockchain_shared_state(this)();
		mon.unlock();
		return result;
	}
	
	public boolean addSummaryBlock(int random)
	//@ requires [_]CBlockchainInv(this) &*& random >= 0 &*& [_] System.out |-> ?o &*& o != null;
  	//@ ensures [_]CBlockchainInv(this);
	{
		mon.lock();
    		//@ open CBlockchain_shared_state(this)();
    		if( !chain.isAvailable() ) {
		    //@ close CBlockchain_shared_state(this)();
		    needsummary.await();
		    //@ open CBlockchain_needsSummary(this)();
		}
		
		boolean result = chain.addSummaryBlock(random);
		
		if( !chain.isAvailable() ) {
		   //@ close CBlockchain_needsSimple(this)();
    		   needsimple.signal();
    		    //@ open CBlockchain_shared_state(this)();
		}
		//@ close CBlockchain_shared_state(this)();
		mon.unlock();
		return result;
	}
	
	public boolean verifyTransactions(Transaction[] ts)
	//@ requires [_]CBlockchainInv(this) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_);
	//@ ensures [_]CBlockchainInv(this) &*& array_slice_deep(ts, 0, ts.length, TransHash, unit,_,_);
	{
		mon.lock();
    		//@ open CBlockchain_shared_state(this)();
		boolean result = chain.verifyTransactions(ts);
		//@ close CBlockchain_shared_state(this)();
		mon.unlock();
		return result;
	}
}
