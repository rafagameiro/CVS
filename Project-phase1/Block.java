/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

©2020 João Costa Seco, Eduardo Geraldo

Students
	António Ferraz nº50110
	Rafael Gameiro nº50677
*/



/* There are auxiliary functions and lemmas to assist in the verification of the code below. */
/*@
	fixpoint int sum(list<int> vs) {
		switch(vs) {
			case nil: return 0;
			case cons(h, t): return (h + sum(t));
		}
	}	
	
	lemma_auto(sum(append(xs, ys))) void sum_append(list<int> xs, list<int> ys)
	requires true;
	ensures sum(append(xs, ys)) == sum(xs) + sum(ys);
	{
		switch(xs) {
			case nil:
			case cons(h, t): sum_append(t, ys);
		}
	}	
		
	fixpoint int hashOf2(int h1, int h2) {
		return (h1^h2);
	}
	
	fixpoint int hashOf3(int h1, int h2, int h3) {
		return hashOf2(hashOf2(h1,h2),h3);
	}



	
@*/

/* 
   The interface of the blockchain blocks. 

   It contains an instance predicate that is then defined in 
   two subclasses that define a summary block and a simple block. 
   
   This predicate defines the representation invariant for blockchain blocks.
   
*/

interface Block {
	//@ predicate BlockInv(Block p, int hp, int h); 

	static final int MAX_ID = 10;

	int balanceOf(int id);
	//@ requires BlockInv(?p, ?hp, ?h) &*& ValidID(id) == true;
	//@ ensures BlockInv(p, hp, h);

	Block getPrevious();
	//@ requires BlockInv(?p, ?hp, ?h);
	//@ ensures BlockInv(p, hp, h) &*& result == p;

	int getPreviousHash();
	//@ requires BlockInv(?p, ?hp, ?h);
	//@ ensures BlockInv(p, hp, h) &*& result == hp;

	int hash();
	//@ requires BlockInv(?p, ?hp, ?h);
	//@ ensures BlockInv(p, hp, h) &*& result == h;
}
