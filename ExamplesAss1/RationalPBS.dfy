/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2022

   Antonia Lopes

*/

/*
 * A property-based specification of Rational Numbers.
 * It includes two lemmas about gcd that were not (yet) proved. Hopefully, they are true.
 *
 * See https://github.com/dafny-lang/dafny/blob/14c5be902cea21eb994f3e0530200d881f9ce5bc/Test/VerifyThis2015/Problem2.dfy#L9
 * for a different (and much complex) approach to gcd definition with proofs for all lemmas
 */
class Rational {
    // The actual implementation (also called the concrete state)
    /* private */var num: int
    /* private */var den: nat

	// The class invariant 
    predicate Valid()
		reads this;
	{
		
		den != 0 && 		   //property of rationals
		Gcd(Abs(num),den) == 1 //representation invariant
	}

 	// Constructors implementations.  
	// Post-conditions of constructors are specified in terms of observers. 
  
	constructor (n: int)
		ensures Valid()
		ensures Num() == Den() * n
	{
		GcdAnythingOne(Abs(n));
		num, den := n, 1;
	}

	constructor Init(n: int, d: int)
		requires d != 0
		ensures Valid()
		ensures Num() * d ==  Den() * n
	{
		new;
		num, den := reduce(n,d);
	}


	// Method implementations.  
	// Obervers do not have post-conditions.
	// Post-conditions of mutators are specified in terms of observers. 
	// Since specifications only mention the observers, it 
	// allows us to later change the implementation without breaking
	// any client code.
	
	//observers
	function method Num(): int
		requires this.Valid() 
		ensures this.Valid()
		reads this;
	{
		num
	}

	function method Den(): int
		requires this.Valid() 
		ensures this.Valid()
		reads this;
	{
		den
	}

	//mutators
	method Add(other: Rational)
		modifies this;
		requires this.Valid() && other.Valid()
		ensures this.Valid() && other.Valid()
		//to help dafny prove the ensures below
		//use of old in both cases because if this == other, it might get confused
		//use of () on the left hand side so it coincides with the ensures of reduce
		ensures Num() * (old(Den()) * old(other.Den())) ==  
			Den() * (old(Num()) * old(other.Den()) + old(Den()) * old(other.Num()))
	{
		var n := this.num * other.den + this.den * other.num;
		var d := this.den * other.den;
		num, den := reduce (n, d);	
	}

	/* 
	This was the version we wrote in the class; Dafny is not able to prove the last ensures
	function method Equals(other: Rational): bool
		reads this, other
		requires this.Valid() && other.Valid()
		ensures this.Valid() && other.Valid()
		ensures this.Equals(other) ==> this.Num() * other.Den() == this.Den() * other.Num()   
		ensures this.Num() * other.Den() == this.Den() * other.Num() ==> this.Equals(other) 
	{
	    this.num == other.num && this.den == other.den
	}
 	*/

	//In this case, several changes were required
	//1) Since there was no need to have equals used in other contracts, 
	//   it was changed and simply defined as a method
	//2) The ensures was written accordingly 
	//3) A lemma was written (but not proved) stating a result that allows Dafny to validate
	//   the method
	
	//others
	method Equals(other: Rational) returns (eq: bool)
		requires this.Valid() && other.Valid()
		ensures this.Valid() && other.Valid()
		ensures eq <==> this.Num() * other.Den() == this.Den() * other.Num()   
	{
	    eq := this.num == other.num && this.den == other.den;
		assert den!=0 && other.den!=0;
		assert Gcd(Abs(num),Abs(den)) == 1;
		assert Gcd(Abs(other.num),Abs(other.den)) == 1;
		reduceMultpl(this.num, other.den, this.den, other.num);
	}

	
} // End of class Rational



//auxiliary procedure (not included in class since it is not an instance method)

/* private */ method reduce(n: int, d: int) returns (rn: int, rd: int)
	requires d != 0
	ensures rn * d ==  rd * n
	ensures rd > 0
	ensures Gcd(Abs(rn), Abs(rd)) == 1
	ensures d > 0 && Gcd(Abs(n), d) == 1 ==> rn == n && rd == d
{
	var g := Gcd(Abs(n),Abs(d));
	
	//some help needed here
	GcdDivisionNotZero(Abs(n),Abs(d));
	GcdDividesBoth(Abs(n), Abs(d));
	DividesMultiplicationProperty1(Abs(n),Abs(d),g);
	GcdDivisionProperty2(Abs(n),Abs(d),g);  
	
	rn := Abs(n)/g;
	rd := Abs(d)/g;
	if (n > 0 && d < 0) || (d > 0 && n < 0) {
			rn := -rn;
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
	ensures Divides(d,m) <==> m % d == 0
{
	m == d * (m/d)   
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

/****** GCD PROPERTIES  ***/

lemma GcdSym(m: nat, n: nat)
  requires  (n != 0 || m != 0) 
  ensures Gcd(m,n) == Gcd(n,m)  
{
}

lemma GcdAnythingOne(m: int)
	requires m >= 0 
	ensures Gcd(m,1) == 1
{}

lemma GcdDivisionNotZero(m: nat, n: nat)
	ensures n !=0 ==> n/Gcd(m,n) > 0 
	ensures m !=0 ==> m/Gcd(m,n) > 0 
{}

lemma GcdDivides(m: nat, n: nat, gcd: nat)
  decreases m+n;
  requires  (n != 0 || m != 0) && gcd == Gcd(m,n)
  ensures Divides(gcd, m) && Divides(gcd, n) 
{
	if (n == 0){
		assert gcd == m;
		assert Divides(gcd, m);
		assert Divides(gcd, n);
	}
	else if (m == 0){
		assert gcd == n;
		assert Divides(gcd, m);
		assert Divides(gcd, n);
	}
	else if (m == n){
		assert gcd == m;
		assert Divides(gcd, m);
		assert Divides(gcd, n);
	}
	else if (m>n) {
		assert n != 0 && m-n != 0;
		assert gcd == Gcd(m-n,n);
		GcdDivides(m-n, n, gcd);
		assert Divides(gcd, m-n);
		DividesSubstractionProperty(m, n, gcd);
		assert Divides(gcd, m);
		assert Divides(gcd, n);
	}
	else if (m<n) {
		assert (n-m != 0 && m != 0);
		assert gcd == Gcd(m,n-m);
		GcdDivides(m, n-m, gcd);
		DividesSubstractionProperty(n, m, gcd);
		assert Divides(gcd, m);
		assert Divides(gcd, n);
	}
}

lemma GcdDividesBoth(m: nat, n: nat)
  requires n != 0 || m != 0
  ensures Divides(Gcd(m,n), m);
  ensures Divides(Gcd(m,n), n);
  ensures DividesBoth(Gcd(m,n), m, n)  
{
  GcdDivides(m,n,Gcd(m,n));
  GcdDivides(m,n,Gcd(m,n));
}

lemma GcdDivisionProperty(m: nat, n: nat, g: nat)
 	requires n != 0 || m != 0
 	requires g == Gcd(m,n) 
 	requires m/g != 0 || n/g != 0
 	ensures Divides(Gcd(m/g,n/g)*g, n)
{
	GcdDividesBoth(m,n);
	var d := Gcd(m/g,n/g);
	var dg := d * g;
	var qn := ((n/g)/d);
	GcdDividesBoth(m/g,n/g);
	assert n/g == qn * d;
	assert (n/g) * g == qn * d * g;
	DividesMultiplicationProperty2(n,g);
	assert n == qn * d * g;
	assert n == qn * (d * g);
	DividesBasicProperty(n,qn,dg);
	assert Divides(dg, n);
}

lemma GcdDivisionProperty2(m: nat, n: nat, g: nat)
 	requires n != 0 || m != 0
 	requires g == Gcd(m,n) 
 	requires m/g != 0 || n/g != 0
 	ensures Gcd(m/g,n/g) == 1
{
	var d := Gcd(m/g,n/g);

	GcdDivisionProperty(m,n,g);
	assert Divides(d * g, n);

	GcdSym(n,m);
	assert g == Gcd(n,m);
	GcdDivisionProperty(n,m,g);
	GcdSym(n/g,m/g);
	assert Divides(d * g, m);

	assert DividesBoth(d * g, m, n);

	GcdIsMaxDivisor(m,n);

	assert d * g <= g;
	assert d >= 1;
	assert g <= d * g <= g;
	assert d * g == g;
	assert d == 1;
 	assert Gcd(m/g,n/g) == 1; 																	
}


//needs to be proved
lemma GcdIsMaxDivisor(m: nat, n: nat)
 	requires n != 0 || m != 0 
 	ensures forall k:nat :: DividesBoth(k, m, n) ==> k <= Gcd(m,n);
{
	assume forall k:nat :: DividesBoth(k, m, n) ==> k <= Gcd(m,n); 						//REMOVE ME
}

//needs to be proved
lemma reduceMultpl(a:int, b:nat, c:nat, d:int)
	requires b != 0  &&  c != 0 
	requires Gcd(Abs(a), c) == 1 
	requires Gcd(Abs(d), b) == 1
	ensures  (a * b == c * d) ==> (a == b && c == d)
{
	assume  (a * b == c * d) ==> (a == b && c == d); 								//REMOVE ME
}



/****** DIVISION PROPERTIES  ***/

lemma DivisionProperty1(n: nat, m:nat)
	requires m != 0
    ensures  n == (n * m) / m  
{
    var q := (n * m) / m;
    assert 0 <= (n * m) - q * m < m;     //remainder property
    assert 0 <= (n - q) * m < m;	    //distributive laws
    assert 0 <= n - q < m / m;
	//   assert 0 <= n - q < 1;
 	//   assert 0 == n - q;
 	//   assert q == n;
 }

/****** DIVIDES PROPERTIES  ***/


lemma DividesMultiplicationProperty1(m: nat, n: nat, d: nat)
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


lemma DividesMultiplicationProperty2(n: nat, m:nat)
	requires m != 0 && Divides(m,n)
    ensures  m * (n/m) == n 
{
	DividesMultiplicationProperty1(n,m,m);
}

lemma DividesBasicProperty(m: nat, q: nat, d: nat)  
	requires d != 0;
	requires m == q * d;
	ensures Divides(d, m);
{
	DivisionProperty1(q, d);
	assert q == m/d;
}


lemma DividesSubstractionProperty(m: nat, n: nat, d: nat)  
	requires m > n && d != 0;
	requires Divides(d, m-n) && Divides(d, n);
	ensures Divides(d, m);
{
	var q := (m-n)/d;
	var qn := n/d;
	assert m-n == q * d;
	assert n == qn * d;
	assert m-n+n == q * d + qn * d;
	assert m-n+n == (q + qn) * d;
	assert m == (q + qn) * d;
	DividesBasicProperty(m, q+qn, d);  
}
