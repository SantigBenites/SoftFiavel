method Divide(x: nat, y: nat) returns (q: nat, r: nat)
{
  q := 0;
  r := x;
  while r >= y {
    r := r - y;
    q := q + 1;
  }
}

method ProductWithIncAndDec (m: nat, n: nat) returns (res: nat)
  ensures res == m * n;
{
  var m1: nat := m; res := 0;
  while m1 != 0 {
    var n1: nat := n;
    while n1 != 0 {
      res := res + 1;
      n1 := n1 - 1;
    }
    m1 := m1 - 1;
  }
}

method BitwiseAdd (a0 : int, b0 : int) returns (c : int)
  requires a0 >= 0 && b0 >= 0;
  ensures c == a0 + b0;
{
  c := 0;
  var a, b, g, m := a0, b0, 1, 0;
  while a > 0 || b > 0 {
    m := m + a % 2 + b % 2;
    a := a / 2;
    b := b / 2;
    c := c + g * (m % 2);
    g := 2 * g;
    m := m / 2;
  }
 c := c + g * m;
}

method AdditiveFactorial(n: nat) returns (u: nat)
  ensures u == Factorial(n);
{
  u := 1;
  var r := 0;
  while r < n {
    var v := u;
    var s := 1;
    while s <= r {
      u := u + v;
      s := s + 1;
    }
    r := r + 1;
  }
}
function Factorial(n: nat): nat  
  requires n > 0
{
  if n == 1 then 1 else n * Factorial(n-1) 
}

method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index <= a.Length;
  ensures index < a.Length ==> a[index] == key;
  ensures index == a.Length ==> forall k :: 0 <= k < index ==> a[k] != key
{
  index := 0;
  while index < a.Length && a[index] != key {
    index := index + 1;
  }
}

method BinarySearch(a: array<int>, key: int) returns (index: int)
  // The array is sorted
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j];
  // If the result is non-negative, then a[index] == key
  ensures 0 <= index ==> index < a.Length && a[index] == key;
  // If the result is negative, then the key is not in the array
  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != key;
{
  var low, high := 0, a.Length;
  while low < high
  {
    var mid := (low + high) / 2;
    if a[mid] < key { low := mid + 1; }
    else if key < a[mid] { high := mid; }
    else { return mid; }
  }
  return -1;
}

method ComputeSum(a: array<int>) returns (sum: int)
{
  var i := 0;
  sum := 0;
  while (i < a.Length)
  {
    sum := sum + a[i];
    i := i + 1;
  }
}

method FindMaxFrequency(v: array<int>) returns (maxElt: int, count: int)
  requires v.Length >= 1; 
  ensures countOccurrences(v, maxElt, v.Length) == count;
  ensures forall j :: 0 <= j < v.Length ==> countOccurrences(v, v[j], v.Length) <= count; 
{
   var i := 0;
   var frequencies := map [];
   while i < v.Length {
     if v[i] in frequencies {
       var prev_frequency := frequencies[v[i]];
       frequencies := frequencies[v[i] := prev_frequency + 1];
     } else {
       frequencies := frequencies[v[i] := 1];
     }
     i := i + 1;
  }
  i := 0;
  maxElt := v[0];
  while i < v.Length {
    if frequencies[v[i]] > frequencies[maxElt] {
      maxElt := v[i];
     }
     i := i + 1;
  }
  count := frequencies[maxElt];
}

function countOccurrences(v: array<int>, elt: int, length: nat) : nat
  requires length <= v.Length;
  ensures !isIn(v,elt,length) ==> countOccurrences(v,elt,length) == 0;
  reads v;
{
  if length == 0 then 0
  else countOccurrences(v, elt, length-1) + 
  	if v[length-1] == elt then 1 else 0
}

predicate isIn(v: array<int>, elt: int, length: nat){
  //todo: define me
  true
}

method NInRow(a: array<int>, n: nat, x: int) returns (found: bool, index: nat) 
{
  found, index := false, 0;
  var i, count := 0, 0;
  while i < a.Length && count < n
  {
    if a[i] == x {
      if count == 0 { index := i; }
      count := count + 1;
    }
    else { count, index := 0, 0; }
    i := i + 1;
  }    
  found := count >= n;
} 