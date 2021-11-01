// Source code to accompany Dafny worksheet
//
// Author: John Wickerson

method triangle(n:int) returns (t:int)
  requires n >=0
  ensures t == n * (n+1) / 2 
{
  t := 0;
  var i := 0;
  while i < n
    invariant i <= n
    invariant t == i * (i+1) / 2
    decreases n - i
  {
    i := i+1;
    t := t+i;
  }
  return t;                         
}

method max (a:int, b:int) returns (r:int) 
  ensures r >= a
  ensures r >= b
  ensures r == a || r == b
{
  if a>b {
    return a;
  } else {
    return b;
  }
}

predicate contains_upto(A:array<int>, hi:int, v:int) 
  reads A
  requires hi <= A.Length
{
  exists j :: 0 <= j < hi && v == A[j]
}

predicate contains(A:array<int>, v:int) 
  reads A
{
  contains_upto(A, A.Length, v)
}

method maxarray (A:array<int>) returns (r:int) 
  requires A.Length > 0
  ensures contains(A, r)
  ensures forall j :: 0 <= j < A.Length ==> r >= A[j]
{
  r := A[0];
  var i := 1;
  while i < A.Length 
    invariant 1 <= i <= A.Length
    invariant contains_upto(A, i, r)
    invariant forall j :: 0 <= j < i ==> r >= A[j]
    decreases A.Length - i
  {
    if r < A[i] {
      r := A[i];
    }
    i := i+1;
  }
  assert i == A.Length;
}

method Main() {
  var m:int := max(3,5);
  print m, "\n";
}