/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

�2020 Jo�o Costa Seco, Eduardo Geraldo

Students
	Ant�nio Ferraz n�50110
	Rafael Gameiro n�50677
*/

/*@
	predicate ValidCheckpoint(int[] b) = b.length == Block.MAX_ID;
@*/

/* 
   The class of blockchain summary blocks. 

   It contains the definition for the instance predicate that instantiate
   the predicate defined in the interface. 
   
   This predicate defines the representation invariant for blockchain summary blocks.
   
*/

class SummaryBlock implements Block {
	/*@ predicate BlockInv(Block p, int hp, int h) =
			this.previous |-> p
		&*& this.hashPrevious |-> hp
		&*& this.random |-> ?r
		&*& this.balances |-> ?a
		&*& isBlock(p,hp)
		&*& array_slice(a,0,a.length,?balances)
		&*& h == hashOf3(sum(balances),hp, r);
	@*/
	
	static int hashBalances(int[] balances)
	//@requires array_slice(balances, 0, balances.length, ?elems);
	//@ensures array_slice(balances, 0, balances.length, elems);
	{
		int balHash = 0;
		int i = 0;

		while(i < balances.length)
		/*@ invariant
			0 <= i &*& i <= balances.length
			&*& array_slice(balances, 0, balances.length, elems)
			&*& balHash == sum(take(i,elems));
		@*/
		{
			int tmp = balances[i];
			balHash = balHash + tmp;
			//@ length_drop(i, elems);
			//@ take_one_more(i, elems);
			i++;
		}
		return balHash;
	}
	

	private Block previous;
	private int hashPrevious;
	private int random;
	private int balances[];
	
	public SummaryBlock(Block previous, int r, int balances[]) 
	/*@ requires
		    isBlock(previous, ?h)
		&*& array_slice(balances,0,balances.length,_)
		&*& ValidCheckpoint(balances);
	@*/
	//@ ensures BlockInv(previous, h, _);
	{
		//@ open isBlock(previous, h);
		this.previous = previous;
		this.hashPrevious = previous == null ? 0 : previous.hash();;
		this.random = r;
		this.balances = balances;
	}

	public int balanceOf(int id)
	//@ requires BlockInv(?p, ?hp, ?h) &*& ValidID(id) == true;
	//@ ensures BlockInv(p, hp, h);
	{
		if(id >= balances.length || id < 0)
			return -1;
		else {
			int bal = balances[id];
			//@ assert this.balances |-> ?b;
			//@ assert array_slice (b, 0, b.length, ?elems);
			//@ bal == nth(id, elems);
			return bal;
		}
	}

	public Block getPrevious()
	//@ requires BlockInv(?p, ?hp, ?h);
	//@ ensures BlockInv(p, hp, h) &*& result == p;
	{
		return previous;
	}

	public int getPreviousHash()
	//@ requires BlockInv(?p, ?hp, ?h);
	//@ ensures BlockInv(p, hp, h) &*& result == hp;
	{
		return hashPrevious;
	}
	
	public int hash()
	//@ requires BlockInv(?p, ?hp, ?h);
	//@ ensures BlockInv(p, hp, h) &*& result == h;
	{
		int balHash = 0;
		int i = 0;

		//@ open BlockInv(p, hp, h);
		//@ assert this.balances |-> ?b;
		//@ assert array_slice(b, 0, b.length, ?items);
		//@ assert this.random |-> ?r;
		while(i < balances.length)
		/*@ invariant
				this.balances |-> b
			&*& this.previous |-> p
			&*& this.hashPrevious |-> hp
			&*& this.random |-> r
			&*& 0 <= i &*& i <= b.length
			&*& isBlock(p,hp)
			&*& array_slice(b, 0, b.length, items)
			&*& balHash == sum(take(i,items));
		@*/
		{
			int tmp = balances[i];
			balHash = balHash + tmp;
			//@ length_drop(i, items);
			//@ take_one_more(i, items);
			i++;
		}	
		return ((balHash ^ this.hashPrevious) ^ this.random);
	}
}
