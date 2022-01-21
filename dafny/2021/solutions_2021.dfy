// Dafny coursework solutions
// Autumn term, 2021
//
// Authors: John Wickerson


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

// Task 1. Difficulty: *
method create_multiples_of_two(A:array<int>)
ensures forall n :: 0 <= n < A.Length ==> A[n] == 2*n
modifies A
{
  var i := 0;
  while i < A.Length 
  invariant 0 <= i <= A.Length
  invariant forall n :: 0 <= n < i ==> A[n] == 2*n
  {
    A[i] := 2 * i;
    i := i + 1;
  }
}

// Task 2. Difficulty: **
predicate partitioned(A:array<int>, index:int) 
  reads A 
  requires 0 <= index <= A.Length
{
  forall i,j :: 0 <= i < index <= j < A.Length ==> A[i] <= A[j]
}

method exchange_sort (A:array<int>)
ensures sorted(A)
modifies A
{
  var i := 0;
  while i < A.Length - 1
  invariant 0 < A.Length ==> 0 <= i < A.Length
  invariant 0 < A.Length ==> partitioned(A, i)
  invariant sorted_between(A,0,i+1); 
  {
    var j := i + 1;
    while j < A.Length
    invariant i < j <= A.Length
    invariant partitioned(A, i)
    invariant sorted_between(A,0,i+1); 
    invariant forall k :: i <= k < j ==> A[i] <= A[k]
    {
      if A[i] > A[j] {
        A[i], A[j] := A[j], A[i];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

// Task 3. Difficulty: **
method fung_sort (A:array<int>)
ensures sorted(A)
modifies A 
{
  var i := 0;
  while i < A.Length 
  invariant i <= A.Length
  invariant sorted_between (A, 0, i)
  {
    var j := 0;
    while j < A.Length
    invariant j <= A.Length 
    invariant sorted_between (A, 0, i)
    invariant 0 < j ==> A[j-1] <= A[i]
    invariant i <= j ==> sorted_between (A, 0, i+1)
    {
      if A[i] < A[j] {
        A[i], A[j] := A[j], A[i];
      }
      j := j+1;
    }
    i := i+1;
  }
}

// Task 4. Difficulty: ***
predicate odd_sorted(A:array<int>, hi:int)
  reads A
{
  forall i :: 0 <= i ==> 2*i+2 < hi <= A.Length ==> A[2*i + 1] <= A[2*i+2]
}

method odd_even_sort(A:array<int>)
  ensures sorted(A)
  modifies A
  decreases *
{
  var is_sorted := false;
  while !is_sorted 
  invariant is_sorted ==> sorted(A)
  decreases *
  {
    is_sorted := true;
    var i := 0;
    while 2*i+2 < A.Length
    invariant 0 < A.Length ==> 0 <= 2*i < A.Length
    invariant odd_sorted (A, 2*i+1)
    {
      if A[2*i+2] < A[2*i+1] {
        A[2*i+1], A[2*i+2] := A[2*i+2], A[2*i+1];
        is_sorted := false;
      }
      i := i+1;
    }
    i := 0;
    while 2*i+1 < A.Length
    invariant 0 <= 2*i <= A.Length
    invariant is_sorted ==> odd_sorted (A, A.Length)
    invariant is_sorted ==> 2*i+1 < A.Length ==> sorted_between(A, 0, 2*i+1);
    invariant is_sorted ==> 2*i+1 >= A.Length ==> sorted_between(A, 0, A.Length);
    {
      if A[2*i+1] < A[2*i] {
        A[2*i], A[2*i+1] := A[2*i+1], A[2*i];
        is_sorted := false;
      }
      i := i+1;
    }
  }
}


// Task 5. Difficulty: ***
method bubble_sort3(A:array<int>)
  ensures sorted(A)
  modifies A
  decreases *
{
  var stable := false;
  while !stable
  invariant stable ==> sorted(A)
  decreases *
  //decreases entropy(A)
  {
    stable := true;
    var j := 0;
    while 2*j+2 <= A.Length
    invariant stable ==> sorted_between(A, 0, 2*j+1)
    invariant stable ==> 2*j+2 == A.Length + 2 ==> sorted_between(A, 0, A.Length)
    invariant 2*j+2 <= A.Length + 2
    decreases A.Length - j
    {
      if 2*j+2 == A.Length {
        if A[2*j+1] < A[2*j] {
          A[2*j+1], A[2*j] := A[2*j], A[2*j+1];
          stable := false;
        }
      } else {
        if A[2*j+1] < A[2*j] {
          A[2*j+1], A[2*j] := A[2*j], A[2*j+1];
          stable := false;
        }
        if A[2*j+2] < A[2*j+1] {
          A[2*j+2], A[2*j+1] := A[2*j+1], A[2*j+2];
          stable := false;
        }
        if A[2*j+1] < A[2*j] {
          A[2*j+1], A[2*j] := A[2*j], A[2*j+1];
          stable := false;
        }
      }
      j := j + 1;
    }
  }
}

// Task 5, bonus
function method entropy_elem(A:array<int>, i:int, j:int) : int 
reads A
requires 0 <= i < j <= A.Length
ensures entropy_elem(A, i, j) >= 0
decreases A.Length - j
{
  if j == A.Length then 0 else
  entropy_elem(A, i, j+1) + (if A[i] > A[j] then 1 else 0)
}

function method entropy_from(A:array<int>, i:int) : int
reads A
requires 0 <= i <= A.Length
ensures entropy_from(A, i) >= 0
decreases A.Length - i
{
  if i == A.Length then 0 else
  entropy_elem(A, i, i+1) + entropy_from(A, i + 1)
}

function method entropy(A:array<int>) : int 
reads A
ensures entropy(A) >= 0
{
  entropy_from(A, 0)
}

method print_array(A:array<int>) 
{
  var i := 0;
  while i < A.Length {
    print A[i];
    i := i + 1;
  }
}

method Main() 
decreases *
{
  var A:array<int> := new int[7] [4,0,1,9,7,1,2];
  print "Before: "; print_array(A); print "\n";
  exchange_sort(A);
  print "After:  "; print_array(A); print "\n";
}