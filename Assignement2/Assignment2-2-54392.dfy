//Exercicio 1
method Countdigits_1(n:nat) returns (d: nat)
requires n > 0
ensures d == digits(n);

{
    var x := n ;
    var k := 0 ;
    while x >= 10
        invariant x >= 1 ==> digits(x) + k == digits(n);
        invariant 1 <= x <= n;
    {
        x := x / 10;
        k := k + 1;
    }
    d := k + 1;
}


//Exercise 2
method Countdigits_2(n:nat) returns (d: nat)
requires n > 0
ensures d > 0;
ensures d == digits(n);
ensures exp(10,d-1) <= n < exp(10,d);
{
    var x := n ;
    var k := 0 ;
    while x >= 10
        invariant x >= 1 ==> digits(x) + k == digits(n);
        invariant 1 <= x <= n;        
    { 
        x := x / 10;
        k := k + 1;
    }
    d := k + 1;
    digitLemma(n,d);
    
}

//Exercise temp

lemma digitLemma(n:nat,d:nat)
requires d == digits(n)
requires n > 0
ensures exp(10,d-1) <= n < exp(10,d);
{
}

function digits(n:nat) :int
//requires n > 0
decreases n
//ensures exp(10,digits(n)-1) <= n < exp(10,digits(n));
ensures digits(n)  > 0;
{
    if n >= 10 then
        1 + digits(n / 10)
    else 
        1 
}

function exp(x: nat, n: nat): int
requires x != 0
decreases n;
{   
    if n == 0 then
        1
    else 
        x * exp(x, n-1)
}


method Main() 
{

    var a := Countdigits_1(1232);
    print a; print '\n';
}