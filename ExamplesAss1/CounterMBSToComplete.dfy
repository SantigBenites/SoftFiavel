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
class {: autocontracts} Counter {
	//The model
	//ghost var 

   // The actual implementation (also called the concrete state)
	/* private */var inc: nat
    /* private */var dec: nat
	
	// The class invariant 
    predicate Valid()
	{
		true //toComplete
		//add representation invariant
	}

    constructor ()
	{
		inc, dec := 0, 0;
		//add ghost code
	}
	
	// Method implementations. 
	method Inc()
	{
		inc := inc + 1;
		//add ghost code
	}
	method Dec()
	{
		dec := dec + 1;
		//add ghost code
	}
	method Clear()
	{
    	inc, dec := 0, 0;
		//add ghost code
	}
	method Get() returns (n: int)
	{
		n := inc - dec;
	}
	method Set(n: int)
	{
 		//toComplete
		//add ghost code
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