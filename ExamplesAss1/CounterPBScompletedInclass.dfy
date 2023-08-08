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
 * Exercise: write a property-based specification for this class
 */
class {: autocontracts} Counter {

   // The actual implementation (also called the concrete state)
	/* private */var inc: nat
    /* private */var dec: nat
	
	// The class invariant 
    predicate Valid()
	{
		true //toComplete
	}

	// Observers
	function method Get(): int
	{
		inc - dec
	}

    constructor ()
		ensures Get() == 0;
	{
		inc, dec := 0, 0;
	}
	
	// Method implementations. 
	method Inc()
		ensures Get() == old(Get()) + 1;
	{
		inc := inc + 1;
	}
	method Dec()
		ensures Get() == old(Get()) - 1;
	{
		dec := dec + 1;
	}

	method Clear()
		ensures Get() == 0;
	{
    	inc, dec := 0, 0;
	}
	

	method Set(n: int)
		ensures Get() == n;
	{
		if (n < 0 ){
			inc, dec := 0, -n;
		}
		else{
			inc, dec := n, 0;
		}
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