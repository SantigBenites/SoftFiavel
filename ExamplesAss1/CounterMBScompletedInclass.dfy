/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2022

   Antonia Lopes

   Credits: Cesare Tinelli-CS:5810-University of Iowa
   and Dafny Tutorial
*/

/*
 * A class Counter.
 * Exercise: 
 * 	1. write a model-based specification for this class 
 *  2. remove the {: autocontracts} and add what is necessary so it checks
 */
class Counter {
	//The model
	//ghost var 
	ghost var value: int;

   // The actual implementation (also called the concrete state)
	/* private */var inc: nat
    /* private */var dec: nat
	
	// The class invariant 
    predicate Valid()
		reads this;
	{
		//representation invariant
		value == inc - dec
	}

    constructor ()
		ensures value == 0;
		ensures Valid();
	{
		inc, dec := 0, 0;
		value := 0; //ghost code
	}
	
	// Method implementations. 
	method Inc()
		modifies this;
		requires Valid(); ensures Valid();
		ensures value == old(value) + 1;
	{
		inc := inc + 1;
		value := inc - dec; //ghost code
	}
	method Dec()
		modifies this;
		requires Valid(); ensures Valid();
		ensures value == old(value) - 1;
	{
		dec := dec + 1;
		value := inc - dec; //ghost code
	}
	method Clear()
		modifies this;
		requires Valid(); ensures Valid();
		ensures value == 0;
	{
    	inc, dec := 0, 0;
		value := inc - dec; //ghost code
	}
	method Get() returns (n: int)
		requires Valid(); ensures Valid();
		ensures n == value;
	{
		n := inc - dec;
	}
	method Set(n: int)
		modifies this;
		requires Valid(); ensures Valid();
		ensures n == value;
	{
		if (n < 0 ){
			inc, dec := 0, -n;
		}
		else{
			inc, dec := n, 0;
		}
		value := inc - dec; //ghost code
	}
}

method Main () 
{
    var c := new Counter();  
	
	var val :=  c.Get(); 
    assert (val == 0);     
    
	c.Dec();c.Dec();
	val :=  c.Get(); 
	assert (val == -2);

	c.Inc(); c.Inc(); c.Inc();
	val :=  c.Get(); 
    assert (val == 1);
   	
	c.Set(3);
	val :=  c.Get(); 
    assert (val == 3);
}