// Dafny coursework solutions
// Autumn term, 2019
//
// Authors: John Wickerson and Matt Windsor

predicate sorted_between(A:array<int>, lo:int, hi:int)
  reads A
  requires 0 <= lo <= hi <= A.Length
{
  forall m,n :: lo <= m < n < hi ==> A[m] <= A[n]
}

// Task 1
predicate sorted(A:array<int>)
  reads A
{
  sorted_between(A,0,A.Length)
}

predicate partitioned(A:array<int>, index:int) 
  reads A 
  requires 0 <= index <= A.Length
{
  forall i,j :: 0 <= i < index <= j < A.Length ==> A[i] <= A[j]
}

// Task 2
method bubble_sort(A:array<int>)
  ensures sorted(A)
  modifies A
{
  var i := 0;
  while i < A.Length 
    invariant 0 <= i <= A.Length
    invariant partitioned(A, A.Length - i)
    invariant sorted_between(A, A.Length - i, A.Length)
    decreases A.Length - i
  {
    var j := 1;
    while j < A.Length - i
      invariant 0 <= i <= A.Length
      invariant 0 < j <= A.Length - i
      invariant partitioned(A, A.Length - i)
      invariant sorted_between(A, A.Length - i, A.Length)
      invariant forall m :: 0 <= m < j-1 ==> A[m] <= A[j-1]
      decreases A.Length - j
    {
      if A[j-1] > A[j] {
        A[j-1], A[j] := A[j], A[j-1];
      }
      j := j+1;
    }
    i := i+1;
  }
}

// Task 3
method selection_sort(A:array<int>)
  ensures sorted(A)
  modifies A
{
  var i := 0;
  while i < A.Length
    invariant 0 <= i <= A.Length
    invariant sorted_between(A, 0, i)
    invariant partitioned(A, i)
    decreases A.Length - i 
  {
    var k := i;
    var j := i+1;
    while j < A.Length
      invariant 0 <= i <= k < j <= A.Length
      invariant sorted_between(A, 0, i)
      invariant partitioned(A, i)
      invariant forall n :: i <= n < j ==> A[k] <= A[n]
      decreases A.Length - j
    {
      if A[k] > A[j] {
        k := j;
      }
      j := j+1;
    }
    A[k], A[i] := A[i], A[k];
    i := i + 1;
  }
}

// Task 4
method insertion_sort(A:array<int>)
  ensures sorted(A)
  modifies A
{
  var i := 0;
  while i < A.Length 
    invariant 0 <= i <= A.Length
    invariant sorted_between(A, 0, i)
    decreases A.Length - i
  {
    var j := i;
    var tmp := A[j];
    while 1 <= j && tmp < A[j-1]
      invariant 0 <= j <= i <= A.Length
      invariant forall l :: j <= l < i ==> tmp < A[l]
      invariant sorted_between(A, 0, i)
      invariant j < i ==> sorted_between(A, 0, i+1)
      decreases j
    {
      A[j] := A[j-1];
      j := j-1;
    }
    A[j] := tmp;
    i := i+1;
  }
}

// Task 5
method shellsort(A:array<int>)
  modifies A
  ensures sorted(A)
{
  var stride := A.Length / 2;
  while 0 < stride
    invariant 0 <= stride
    invariant stride == 0 ==> sorted(A)
    decreases stride
  {
    var i := 0;
    while i < A.Length 
      invariant 0 <= i <= A.Length
      invariant stride==1 ==> sorted_between(A, 0, i)
      decreases A.Length - i
    {
      var j := i;
      var tmp := A[j];
      while stride <= j && tmp < A[j-stride]
        invariant 0 <= j <= i <= A.Length
        invariant stride==1 ==> forall l :: j <= l < i ==> tmp < A[l]
        invariant stride==1 ==> sorted_between(A, 0, i)
        invariant stride==1 ==> j < i ==> sorted_between(A, 0, i+1)
        decreases j
      {
        A[j] := A[j-stride];
        j := j-stride;
      }
      A[j] := tmp;
      i := i+1;
    }
    stride := stride / 2;
  }
}

// Task 6
method john_sort(A:array<int>)
  ensures sorted(A)
  modifies A
{
  var i := 0; 
  while i < A.Length
    invariant 0 <= i <= A.Length
    invariant forall j :: 0 <= j < i ==> A[j] == 42
    decreases A.Length - i
  {
    A[i] := 42;
    i := i + 1;
  }
}

method Main() {
  var A:array<int> := new int[7] [4,0,1,9,7,1,2];
  print "Before: ", A[0], A[1], A[2], A[3], 
        A[4], A[5], A[6], "\n";
  bubble_sort(A);
  print "After:  ", A[0], A[1], A[2], A[3], 
        A[4], A[5], A[6], "\n";
}