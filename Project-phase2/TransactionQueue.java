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

    predicate_ctor CQueue_shared_state(TransactionQueue tq)() = tq.q |-> ?q &*& q != null &*& QueueInv(q,P,_,_);

    predicate_ctor CQueue_nonempty(TransactionQueue tq)() = tq.q |-> ?q &*& q != null &*& QueueInv(q,P,?n,_) &*& n > 0;

    predicate_ctor CQueue_nonfull(TransactionQueue tq)() = tq.q |-> ?q &*& q != null &*& QueueInv(q,P,?n,?m) &*& n < m;

    predicate CQueueInv(TransactionQueue tq;) =
            tq.mon |-> ?l
    	&*& tq.notempty |-> ?ce
    	&*& tq.notfull |-> ?cf

    	&*& l != null
    	&*& ce != null
    	&*& cf != null

    	&*& lck(l, 1, CQueue_shared_state(tq))
    	&*& cond(ce, CQueue_shared_state(tq), CQueue_nonempty(tq))
    	&*& cond(cf, CQueue_shared_state(tq), CQueue_nonfull(tq));

@*/

class TransactionQueue {

  Queue q;

  ReentrantLock mon;
  Condition notempty;
  Condition notfull;

  TransactionQueue(int size)
  //@ requires size > 0;
  //@ ensures CQueueInv(this);
  {
    q = new Queue(size);
    //@ close CQueue_shared_state(this)();
    //@ close enter_lck(1, CQueue_shared_state(this));
    mon = new ReentrantLock();
    //@ close set_cond(CQueue_shared_state(this), CQueue_nonempty(this));
    notempty = mon.newCondition();
    //@ close set_cond(CQueue_shared_state(this), CQueue_nonfull(this));
    notfull = mon.newCondition();
  }

  void enqueue(Transaction v)  
  //@ requires [_]CQueueInv(this) &*& v != null &*& TransInv(v,_,_,_);
  //@ ensures [_]CQueueInv(this);
  {
    mon.lock();
    //@ open CQueue_shared_state(this)();
    if( q.isFull() ) {
      //@ close CQueue_shared_state(this)();
      notfull.await();
      //@ open CQueue_nonfull(this)();
    }
    //@ open QueueInv(q,_,_,_);
    q.enqueue(v);
    //@ close CQueue_nonempty(this)();
    notempty.signal();
    mon.unlock();
  }

  Transaction dequeue() 
  //@ requires [_]CQueueInv(this);
  //@ ensures [_]CQueueInv(this) &*& TransHash(unit, result, _);
  {
    mon.lock();
    //@ open CQueue_shared_state(this)();
    if( q.isEmpty() ) {
      //@ close CQueue_shared_state(this)();
      notempty.await();
      //@ open CQueue_nonempty(this)();
    }
    //@ open QueueInv(q,_,_,_);
    Transaction t = q.dequeue();
    //@ close CQueue_nonfull(this)();
    notfull.signal();
    mon.unlock();
    return t;
  }
}
