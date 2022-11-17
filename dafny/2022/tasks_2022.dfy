// Dafny coursework tasks
// Autumn term, 2022
//
// Authors: John Wickerson

method countsquares(n:nat) returns (result:nat)
  //ensures result == ...
{
  var i := 0;
  result := 0;
  while i < n {
    i := i + 1;
    result := result + i * i;
  }
}

method countsquares2(n:nat) returns (result:nat)
  // ensures result == ...
{
  var i := n;
  result := 0;
  while i > 0 {
    result := result + i * i;
    i := i - 1;
  }
}

predicate sorted(A:array<int>)
  reads A
{
	forall m,n :: 0 <= m < n < A.Length ==> A[m] <= A[n]
}

method binarysearch_between(A:array<int>, v:int, lo:int, hi:int) returns (result:bool)
  requires false // Please remove this line.
{
  if lo == hi {
    return false;
  } 
  var mid:int := (lo + hi) / 2;
  if v == A[mid] {
    return true;
  }
  if v < A[mid] {
    result := binarysearch_between(A, v, lo, mid);
  }
  if v > A[mid] {
    result := binarysearch_between(A, v, mid+1, hi);
  }
}

method binarysearch(A:array<int>, v:int) returns (result:bool)
  requires false // Please remove this line.
{
  result := binarysearch_between(A, v, 0, A.Length);
}

method binarysearch_iter(A:array<int>, v:int) returns (result:bool)
{
  // Please provide an implementation of this method. 
}

method partition(A:array<int>, lo:int, hi:int) returns (pivot:int)
  requires 0 <= lo < hi <= A.Length
  ensures 0 <= lo <= pivot < hi
  ensures forall k :: (0 <= k < lo || hi <= k < A.Length) ==> old(A[k]) == A[k]
  modifies A
{
  pivot := lo;
  var i := lo+1;
  while i < hi
    invariant 0 <= lo <= pivot < i <= hi
    invariant forall k :: (0 <= k < lo || hi <= k < A.Length) ==> old(A[k]) == A[k]
    decreases hi - i
  {
    if A[i] < A[pivot] {
      var j := i-1;
      var tmp := A[i];
      A[i] := A[j];
      while pivot < j
        invariant forall k :: (0 <= k < lo || hi <= k < A.Length) ==> old(A[k]) == A[k]
        decreases j
      {
        A[j+1] := A[j];
        j := j-1;
      }
      A[pivot+1] := A[pivot];
      A[pivot] := tmp;
      pivot := pivot+1;
    }
    i := i+1;
  }
}

method quicksort_between(A:array<int>, lo:int, hi:int)
  requires 0 <= lo <= hi <= A.Length
  ensures forall k :: (0 <= k < lo || hi <= k < A.Length) ==> old(A[k]) == A[k]
  modifies A
  decreases hi - lo
{
  if lo+1 >= hi { return; }
  var pivot := partition(A, lo, hi);
  quicksort_between(A, lo, pivot);
  quicksort_between(A, pivot+1, hi);
}

method quicksort(A:array<int>)
	modifies A
{
  quicksort_between(A, 0, A.Length);
}

method Main() {
  var A:array<int> := new int[7] [4,0,1,9,7,1,2];
  print "Before: ", A[0], A[1], A[2], A[3], 
        A[4], A[5], A[6], "\n";
  quicksort(A);
  print "After:  ", A[0], A[1], A[2], A[3], 
        A[4], A[5], A[6], "\n";
}
