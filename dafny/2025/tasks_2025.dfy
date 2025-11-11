// Dafny coursework 2025
//
// Authors: John Wickerson

predicate sorted(A:array<int>)
  reads A
{
  forall m,n :: 0 <= m < n < A.Length ==> A[m] <= A[n]
}


method doublesort_from(A:array<int>, lo:int)
{
  if lo + 1 < A.Length {
    doublesort_from(A, lo + 1);
    if A[lo + 1] < A[lo] {
      A[lo], A[lo + 1] := A[lo + 1], A[lo];
    } 
    doublesort_from(A, lo + 1);
  }
}

method doublesort(A:array<int>)
  ensures sorted(A)
{
  doublesort_from(A, 0);
}

method Main() {
  var A:array<int> := new int[7] [4,0,1,9,7,1,2];
  print "Before: ", A[0], A[1], A[2], A[3], 
        A[4], A[5], A[6], "\n";
  doublesort(A);
  print "After:  ", A[0], A[1], A[2], A[3], 
        A[4], A[5], A[6], "\n";
}
