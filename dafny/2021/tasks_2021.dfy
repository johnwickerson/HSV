// Dafny coursework tasks
// Autumn term, 2021
//
// Authors: John Wickerson

predicate sorted(A:array<int>)
  reads A
{
  forall m,n :: 0 <= m < n < A.Length ==> A[m] <= A[n]
}

// Task 1. Difficulty: *
method create_multiples_of_two(A:array<int>)
ensures forall n :: 0 <= n < A.Length ==> A[n] == 2*n
modifies A
{
  // ...
}

// Task 2. Difficulty: **
method exchange_sort (A:array<int>)
ensures sorted(A)
modifies A
{
  var i := 0;
  while i < A.Length - 1 {
    var j := i + 1;
    while j < A.Length {
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
  while i < A.Length {
    var j := 0;
    while j < A.Length {
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
  while !is_sorted {
    is_sorted := true;
    var i := 0;
    while 2*i+2 < A.Length {
      if A[2*i+2] < A[2*i+1] {
        A[2*i+1], A[2*i+2] := A[2*i+2], A[2*i+1];
        is_sorted := false;
      }
      i := i+1;
    }
    i := 0;
    while 2*i+1 < A.Length {
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
  while !stable {
    stable := true;
    var j := 0;
    while 2*j+2 <= A.Length {
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

// Task 6. Difficulty: *
function method get_min(a:int, b:int) : int
{
  if a <= b then a else b
}

method sort3(a:int, b:int, c:int) returns (min:int, mid:int, max:int)
ensures min in {a,b,c}
ensures mid in {a,b,c}
ensures max in {a,b,c}
ensures a in {min, mid, max}
ensures b in {min, mid, max}
ensures c in {min, mid, max}
ensures min <= mid <= max
{
  min := get_min(a, get_min(b,c));
  max := -get_min(-a, get_min(-b,-c));
  mid := a + b + c - max - min;
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