// Dafny coursework solutions
// Autumn term, 2020
//
// Authors: John Wickerson and Matt Windsor

// Task 1
predicate zeroes(A:array<int>)
  reads A
{
  forall i :: 0 <= i < A.Length ==> A[i] == 0
}

method resetArray(A:array<int>)
  ensures zeroes(A)
  modifies A
{
  var i := 0;
  while i < A.Length 
  invariant 0 <= i <= A.Length
  invariant forall j :: 0 <= j < i ==> A[j] == 0
  decreases A.Length - i
  {
    A[i] := 0;
    i := i + 1;
  }
}

predicate sorted_between(A:array<int>, lo:int, hi:int)
  reads A
{
  forall m,n :: 0 <= lo <= m < n < hi <= A.Length ==> A[m] <= A[n]
}
predicate sorted(A:array<int>)
  reads A
{
  sorted_between(A,0,A.Length)
}

predicate partitioned(A:array<int>, index:int) 
  reads A 
{
  forall i,j :: 0 <= i < index <= j < A.Length ==> A[i] <= A[j]
}

// Task 2
method backwards_selection_sort(A:array<int>)
  ensures sorted(A)
  modifies A
{
  var i := A.Length;
  while 0 < i
    invariant 0 <= i <= A.Length
    invariant sorted_between(A, i, A.Length)
    invariant partitioned(A, i)
    decreases i 
  {
    var max := 0;
    var j := 1;
    while j < i
      invariant 0 <= max < j <= i
      invariant forall n :: 0 <= n < j ==> A[n] <= A[max]
      decreases i - j
    {
      if A[max] < A[j] {
        max := j;
      }
      j := j+1;
    }

    A[max], A[i-1] := A[i-1], A[max];
    i := i - 1;
  }
}

// Task 3
method recursive_selection_sort_inner(A:array<int>, i:int)
  requires 0 <= i <= A.Length
  requires sorted_between(A, 0, i)
  requires partitioned(A, i)
  ensures sorted(A)
  modifies A
  decreases A.Length - i
{
  if i == A.Length { 
    return; 
  }
  var k := i;
  var j := i + 1;
  while j < A.Length
    invariant 0 <= i <= k < j <= A.Length
    invariant forall n :: i <= n < j ==> A[k] <= A[n]
    decreases A.Length - j
  {
    if A[k] > A[j] {
      k := j;
    }
    j := j+1;
  }
  A[k], A[i] := A[i], A[k];
  recursive_selection_sort_inner(A, i + 1);
}
method recursive_selection_sort(A:array<int>)
  ensures sorted(A)
  modifies A
{
  recursive_selection_sort_inner(A, 0);
}

// Task 4
method bubble_sort_with_early_stop(A:array<int>) 
  ensures sorted(A)
  modifies A
{
  var stable := false;
  var i := 0;
  while !stable
  invariant 0 <= i <= A.Length + 1
  invariant partitioned(A, A.Length - i)
  invariant sorted_between(A, A.Length - i, A.Length)
  invariant if stable then sorted(A) else i < A.Length + 1
  decreases A.Length - i 
  {
    var j := 0;
    stable := true;
    while j + 1 < A.Length - i
    invariant 0 <= i <= A.Length 
    invariant 0 < A.Length ==> 0 <= j < A.Length
    invariant partitioned(A, A.Length - i)
    invariant sorted_between(A, A.Length - i, A.Length)
    invariant if stable then sorted_between(A, 0, j + 1) else i < A.Length
    invariant forall m :: 0 <= m < j < A.Length ==> A[m] <= A[j]
    invariant A.Length - i <= j ==> partitioned(A, A.Length - i - 1)
    decreases A.Length - j
    {
      if A[j+1] < A[j] {
        A[j], A[j+1] := A[j+1], A[j];
        stable := false;
      }
      j := j+1;
    }
    i := i+1;
  }
}

// Task 5
method cocktail_shaker_sort(A:array<int>)
  ensures sorted(A)
  modifies A
{
  var i := 0;
  while i < A.Length / 2
    invariant i <= A.Length
    invariant partitioned(A, A.Length - i)
    invariant partitioned(A, i)
    invariant sorted_between(A, A.Length - i, A.Length)
    invariant sorted_between(A, 0, i)
    decreases A.Length - i
  {
    var j := i;
    while j < A.Length - i - 1
      invariant j < A.Length - i
      invariant partitioned(A, A.Length - i)
      invariant partitioned(A, i)
      invariant sorted_between(A, A.Length - i, A.Length)
      invariant sorted_between(A, 0, i)
      invariant forall m :: 0 <= m < j ==> A[m] <= A[j]
      decreases A.Length - j 
    {
      if A[j+1] < A[j] {
        A[j], A[j+1] := A[j+1], A[j];
      }
      j := j+1;
    }
    while i < j
      invariant i <= j < A.Length - i
      invariant partitioned(A, A.Length - i)
      invariant partitioned(A, A.Length - i - 1)
      invariant partitioned(A, i)
      invariant sorted_between(A, A.Length - i, A.Length)
      invariant sorted_between(A, 0, i)
      invariant forall m :: j < m < A.Length ==> A[j] <= A[m]
      decreases j
    {
      if A[j-1] > A[j] {
        A[j-1], A[j] := A[j], A[j-1];
      }
      j := j-1;
    }
    i := i+1;
  }
}

method Main() {
  var A:array<int> := new int[7] [4,0,1,9,7,1,2];
  print "Before: ", A[0], A[1], A[2], A[3], 
        A[4], A[5], A[6], "\n";
  recursive_selection_sort(A);
  print "After:  ", A[0], A[1], A[2], A[3], 
        A[4], A[5], A[6], "\n";
}