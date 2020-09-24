/* For this lab, you'll have to implement and verify  a readers-writer lock,
   also known as a multiple readers single writer lock. As the name implies,
   multiple readers can acquire the lock with reading rights, however, it can
   only be held by one writer. Furthermore, it if the lock has been acquired for
   reading, it cannot be acquired for writing and vice-versa.
*/
import java.util.concurrent.locks.*;

/*@

	predicate_ctor MRSW_shared_state (MRSWLock m) () =
   		m.readercount |-> ?r &*& r >= 0 &*& m.busy |-> ?b;

	predicate_ctor MRSW_oktoread (MRSWLock m) () =
   		m.readercount |-> ?r &*& m.busy |-> ?b &*& r >= 0 &*& b == false;

	predicate_ctor MRSW_oktowrite (MRSWLock m) () =
   		m.readercount |-> ?r &*& m.busy |-> ?b &*& r == 0 &*& b == false; 
   
	predicate inv(MRSWLock m) =  
     		m.mon |-> ?l 
     	&*& l!=null 
     	&*& lck(l,1,MRSW_shared_state(m))
     	&*& m.OKtoread |-> ?or 
     	&*& or !=null 
     	&*& cond(or,MRSW_shared_state(m),MRSW_oktoread(m))
     	&*& m.OKtowrite |-> ?ow 
     	&*& ow !=null 
     	&*& cond(ow,MRSW_shared_state(m),MRSW_oktowrite(m));
 
@*/

class MRSWLock {
	
	private int readercount;
	private boolean busy;
	private ReentrantLock mon;
	private Condition OKtoread, OKtowrite;
	
	public MRSWLock(){
		readercount = 0;
		busy = false;
		//@ close CCounter_shared_state(this)();
  		//@ close enter_lck(1,MRSW_shared_state(this));
  		mon = new ReentrantLock();
  		//@ close set_cond(MRSW_shared_state(this),MRSW_oktoread(this));  
  		OKtoread = mon.newCondition();
  		//@ close set_cond(MRSW_shared_state(this),MRSW_oktowrite(this));  
  		OKtowrite = mon.newCondition();
  		//@ close inv(this);
	}
	
	/* 
	 * Aquires this lock for reading, after successfully returned from this
	 * method, the caller has reading rights on the state protected by this
	 * lock.
	 */
	public void readLock ()
	
	{
		mon.enter();
		
		
	}
	
	/* 
	 * Releases the reading lock.
	 */
	public void readUnlock ()
	
	{
	
	}
	
	/*
	 * Acquires this lock for writing, after successfully returned from this
	 * method, the caller has writing rights on the state protected by this
	 * lock.
	 */
	public void writeLock ()
	
	{
		if(readercount > 0 || busy) OKtowrite.wait();
	}

	/*
	 * Releases the writing lock.
	 */
	public void writeUnlock ()
	
	{
	
	}
}
