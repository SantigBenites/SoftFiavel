/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2021

   Antonia Lopes

   Exercise: Write a property-based specification for this class. 
   The class invariant is already given. We will not use auto-contracts 
   in this example.
*/

/*
 * A class for Rational Numbers.
 */
class Rational {

    // The actual implementation (also called the concrete state)
    /* private */var num: int
    /* private */var den: nat

	// The class invariant 
    predicate Valid()
		reads this;
	{
		//representation invariant
		den != 0 
		&& Gcd(Abs(num), den) == 1  
	}

  	// Post-conditions of constructors are specified in terms of observers. 
  
	constructor (n: int)
		ensures Valid()
	{
		GcdOne(Abs(n));
		num, den := n, 1;
	}

	constructor Init(n: int, d: int)
		requires d != 0
		ensures Valid()
	{
		new;
		num, den := reduce(n,d);
	}


	// Method implementations.  
	// Observers do not have post-conditions.
	// Post-conditions of mutators are specified in terms of observers. 
	// Since specifications only mention the observers, it 
	// allows us to later change the implementation without breaking
	// any client code.
	
	//observers
	function method Num(): int
		reads this;
	{
		num
	}

	function method Den(): int
		reads this;
	{
		den
	}

	//mutators
	method Add(other: Rational)
		modifies this;
		requires this.Valid() && other.Valid()
		ensures this.Valid() && other.Valid()
	{
		var n := this.num * other.den + this.den * other.num;
		var d := this.den * other.den;
		num, den := reduce (n, d);
	}

	//others
	function method Equals(other: Rational): bool
		reads this, other
		requires this.Valid() && other.Valid()
		ensures this.Valid() && other.Valid()
	{
	    this.num == other.num && this.den == other.den
	}

	//auxiliary

	/* private */ method reduce(n: int, d: int) returns (rn: int, rd: int)
		requires d != 0
		ensures rn * d ==  rd * n
		ensures rd > 0
		ensures Gcd(Abs(rn), Abs(rd)) == 1
	{
		var g := Gcd(Abs(n),Abs(d));
		
		//some help needed here
		GcdDivisionNotZero(Abs(n),Abs(d));
		GcdDefinition(Abs(n), Abs(d));
		GcdMultiply(Abs(n),Abs(d),g);
		GCDIsMaxDivisor(Abs(n),Abs(d),g);  
		
		rn := Abs(n)/g;
		rd := Abs(d)/g;

		if (n > 0 && d < 0) || (d > 0 && n < 0) {
				rn := -rn;
		} 
	}

 
}

method Main () 
{
    var r := new Rational(3);     
	var n := r.Num();
	var d := r.Den();
	print n; print '/'; print d; print '\n';
	
	var r2 := new Rational.Init(3,6);
	r.Add(r2);
	n := r.Num();
	d := r.Den();
	print n; print '/'; print d; print '\n';

	var r3 := new Rational.Init(6,12);
	var b := r2.Equals(r3);
	print b;
}


/*
	Specification helpers
*/

function method Abs(m: int): nat
{
	if m >= 0 then m else -m
}

predicate Divides(d: nat, m: int)
	requires d != 0
{
	m == d * (m/d)   // eqv m % d == 0
}

predicate DividesBoth(d: nat, m: nat, n: nat)
{
  d != 0 && Divides(d, n) && Divides(d, m)
}

function method Gcd(m: nat, n: nat): nat
	requires n != 0 || m != 0
    decreases m+n;
	ensures Gcd(m,n) > 0;
{ 
        if n == 0 then m
		else if m == 0 then n
		else if (n == m) then n 
        else if (m > n) then Gcd(m-n, n) 
        else Gcd(m, n-m) 
}

/*
	Lemmas and some proofs
*/


//needs to be proved
lemma GcdDefinition(m: nat, n: nat)
  requires n != 0 || m != 0
  ensures DividesBoth(Gcd(m,n), m, n) 
  ensures forall k:nat :: DividesBoth(k, m, n) ==> k <= Gcd(m,n);
{
  assume DividesBoth(Gcd(m,n), m, n);							 //REMOVE ME
  assume forall k:nat :: DividesBoth(k, m, n) ==> k <= Gcd(m,n); //REMOVE ME
}

//needs to be proved
lemma GcdDividesBoth(m: nat, n: nat)
  requires n != 0 || m != 0
  ensures Divides(Gcd(m,n), m) && Divides(Gcd(m,n), n)
{
       if n == 0  
	   {
       		assert m == m * (m/m);
       	}
		else if m == 0  {
			assert m == m * (m/n);
		}
		else if (n == m)  {
			assert m == n * (m/n); 
		}
        else if (m > n)  {
        	GcdDividesBoth(m-n, n);
        }
        else {
			GcdDividesBoth(m, n-m);
		}
	//m == Gcd(m,n) * (m/Gcd(m,n)) 
}


lemma GcdOne(m: int)
	requires m >= 0 
	ensures Gcd(m,1) == 1
{
}

lemma GcdDivisionNotZero(m: nat, n: nat)
	ensures n !=0 ==> n/Gcd(m,n) > 0 
	ensures m !=0 ==> m/Gcd(m,n) > 0 
{
}


lemma GcdMultiply(m: nat, n: nat, d: nat)
	requires d != 0
	requires Divides(d, n) && Divides(d, m)
	ensures n * (m/d) == m * (n/d)
{
	assert m == d * (m/d);
	assert m * (n/d) == d * (m/d) * (n/d); 
	assert n == d * (n/d);
	assert n * (m/d) == d * (n/d) * (m/d);
	assert d * (m/d) * (n/d) == d * (n/d) * (m/d);
}

//needs to be proved
lemma GCDIsMaxDivisor(m: nat, n: nat, g: nat)
 	requires n != 0 || m != 0
 	requires g == Gcd(m,n) 
 	requires m/g != 0 || n/g != 0
 	ensures Gcd(m/g,n/g) == 1
{
 	assume Gcd(m/g,n/g) == 1; //REMOVE ME
}



