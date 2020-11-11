// Dafny coursework tasks
// Autumn term, 2020
//
// Authors: John Wickerson and Matt Windsor

predicate sorted(A:array<int>)
  reads A
{
  forall m,n :: 0 <= m < n < A.Length ==> A[m] <= A[n]
}

// Task 1
method resetArray(A:array<int>)
  ensures zeroes(A)
  modifies A
{
  var i := 0;
  while i < A.Length {
    A[i] := 0;
    i := i + 1;
  }
}

// Task 2
method backwards_selection_sort(A:array<int>)
  ensures sorted(A)
  modifies A
{
  var i := A.Length;
  while 0 < i {
    var max := 0;
    var j := 1;
    while j < i {
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
  modifies A
{
  if i == A.Length { 
    return; 
  }
  var k := i;
  var j := i + 1;
  while j < A.Length {
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
  while !stable {
    var j := 0;
    stable := true;
    while j + 1 < A.Length - i {
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
  while i < A.Length / 2 {
    var j := i;
    while j < A.Length - i - 1 {
      if A[j+1] < A[j] {
        A[j], A[j+1] := A[j+1], A[j];
      }
      j := j+1;
    }
    while i < j {
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