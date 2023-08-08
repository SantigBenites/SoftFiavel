//Exercicio 3.1
method MaxSubArray_1 ( a: array <int>) returns ( best_sum: int )
requires a.Length > 0
{
    best_sum := a[0];
    var i, current_sum := 0,0;
    while i < a.Length 
    {
        current_sum := max(a[i], current_sum + a[i]);
        best_sum := max(best_sum, current_sum);
        i := i + 1;
    }

}

//Exercicio 3.2
method MaxSubArray_2 ( a: array <int>) returns ( best_sum: int )
requires a.Length > 0
ensures forall j,k :: 0 <= j < k < a.Length ==> sum(a,j,k) <= best_sum;  
{

    best_sum := a[0];
    var i, current_sum := 0,0;
    while i < a.Length 
        invariant 0 <= i <= a.Length;
        invariant forall j, k :: 0 <= j < k <= i ==> sum(a,j,k) <= best_sum;
        invariant forall j :: 0 <= j < i ==> sum(a,j,i) <= current_sum;
    {
        current_sum := max(a[i], current_sum + a[i]);
        best_sum := max(best_sum, current_sum);
        i := i + 1;
    }

}

//Excercicio 3.3 (the invariants are wrong (should be right) and the method sum doesnt work for this function)
method MaxSubArray_3 ( a: array <int>) returns (best_sum: int )
requires a.Length > 0;
ensures forall j,k :: 0 <= j < k <= a.Length ==> sum(a,j,k) <= best_sum;
//ensures exists j,k :: 0 <= j < k <= a.Length && sum(a,j,k) == best_sum;
{

    best_sum := a[0];
    ghost var best_start,best_end := 0,0;
    var current_start,current_end:= 0,0;
    var i, current_sum := 0,0;

    while i < a.Length 
        invariant 0 <= i <= a.Length;
        invariant forall j, k :: 0 <= j < k <= i ==> sum(a,j,k) <= best_sum;
        invariant forall j :: 0 <= j < i ==> sum(a,j,i) <= current_sum;
        //invariant exists j,k :: 0 <= j < k < i && sum(a,j,k) == best_sum;
    {
        if current_sum <= 0 {
            current_start := i;
            current_sum := a[i];
        }else{
            current_sum := current_sum + a[i];
        }

        if current_sum > best_sum {
            best_sum := current_sum;
            best_start := current_start;
            best_end := current_end;
        }
        i := i +1;
        current_end := current_end + 1;
    }

}


function method sum(a: array?<int>,i: int,j: int): int
    decreases j;
    requires a != null;
    requires 0 <= i <= j <= a.Length;
    reads a;
{
    if j == i then 0 else sum(a, i, j - 1) + a[j - 1]
}

function func_sum(a: array?<int>, min: int, max:int): int
    requires a != null;
    requires 0 <= min <= max < a.Length;
    reads a;
    decreases max - min;
{
    if min != max then
        func_sum(a, min + 1, max) + a[min]
    else
        a[min]
}


function method max (a:int,b:int): int{if a > b then a else b} 


method Main ( ) {
    var a := new int [5];
    a[0] := 5;
    a[1] := -2;
    a[2] := 10;
    a[3] := -20;
    a[4] := 12;
    var n := MaxSubArray_2(a);
    print a [..];
    print "\t\t";
    print n;
    print "\n";
    a[3] := -2;
    n := MaxSubArray_2(a);
    print a[..];
    print "\t\t";
    print n;
    print "\n";
}