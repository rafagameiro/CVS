public class Account {

  int checking;
  int savings;

  /*@ 
  predicate AccountInv(int c, int s) = 
  	this.checking |-> c 
	&*&
	this.savings |-> s
	&*&
	s >= 0
	&*&
	c >= -s/2;
  @*/

  public Account()
  //@ requires true;
  //@ ensures AccountInv(0, 0);
  {
    savings = 0;
	checking = 0;
  }
  
  public int getBalance()
  //@ requires AccountInv(?c,?s);
  //@ ensures AccountInv(c,s) &*& result == c;
  {
  	return checking;
  }
  
  public void deposit(int amount)
  //@ requires AccountInv(?c,?s) &*& amount >= 0;
  //@ ensures AccountInv(c+amount,s);
  {
  	checking += amount;
  }
  
  public void withdraw(int amount)
  //@ requires AccountInv(?c,?s) &*& amount >= 0 &*& (c >= - s/2 + amount);
  //@ ensures AccountInv(c-amount,s);
  {
  	checking -= amount;
  }
  
  public void save(int amount)
  //@ requires AccountInv(?c,?s) &*& amount >= 0 &*& amount <= 0;
  //@ ensures AccountInv(c-amount,s+amount);
  {
  	checking -= amount;
  	savings += amount;
  }
  
  public void rescue(int amount)
  //@ requires AccountInv(?c,?s) &*& amount >= 0 &*& amount <= 0;
  //@ ensures AccountInv(c+amount,s-amount);
  {
  	checking += amount;
  	savings -= amount;
  }
  
  public static void main(String[] args) 
  //@ requires true;
  //@ ensures true;
  {
  
  	Account ac = new Account();
  	int b = ac.getBalance();
  	//@ assert b == 0; 
  }

}
