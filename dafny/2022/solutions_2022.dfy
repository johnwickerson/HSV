// Dafny coursework solutions
// Autumn term, 2022
//
// Authors: John Wickerson

function pyramid(n:int) : int {
  n * (n + 1) * (2*n + 1) / 6
}

method countsquares(n:nat) returns (result:nat)
  ensures result == pyramid(n)
{
  var i := 0;
  result := 0;
  while i < n 
    invariant i <= n
    invariant result == pyramid(i)
    decreases n - i
  {
    i := i + 1;
    result := result + i * i;
  }
}

method countsquares2(n:nat) returns (result:nat)
  ensures result == pyramid(n)
{
  var i := n;
  result := 0;
  while i > 0 
    invariant 0 <= i
    invariant result == pyramid(n) - pyramid(i)
    decreases i
  {
    result := result + i * i;
    i := i - 1;
  }
}

predicate sorted(A:array<int>)
  reads A
{
	forall m,n :: 0 <= m < n < A.Length ==> A[m] <= A[n]
}

predicate sorted_between(A:array<int>, lo:int, hi:int)
  reads A
{
  forall m,n :: 0 <= lo <= m < n < hi <= A.Length ==> A[m] <= A[n]
}

method binarysearch_between(A:array<int>, v:int, lo:int, hi:int) returns (result:bool)
  requires 0 <= lo <= hi <= A.Length
  requires sorted(A)
  ensures result == (exists i :: lo <= i < hi && A[i] == v)
  decreases hi - lo
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
  requires sorted(A)
  ensures result == (exists i :: 0 <= i < A.Length && A[i] == v)
{
  result := binarysearch_between(A, v, 0, A.Length);
}

method binarysearch_iter(A:array<int>, v:int) returns (result:bool)
  requires sorted(A)
  ensures result == (exists i :: 0 <= i < A.Length && A[i] == v)
{
  var lo:int := 0;
  var hi:int := A.Length;
  while lo < hi 
    invariant 0 <= lo <= hi <= A.Length
    invariant (forall i :: 0 <= i < lo ==> A[i] < v)
    invariant (forall i :: hi <= i < A.Length ==> v < A[i])
    decreases hi - lo
  {
    var mid:int := (lo + hi) / 2;
    if v == A[mid] { return true; }
    if v < A[mid] { hi := mid; }
    if A[mid] < v { lo := mid + 1; }
  }
  return false;
}

predicate partitioned(A:array<int>, index:int) 
  reads A 
  requires 0 <= index <= A.Length
{
  forall i,j :: 0 <= i < index <= j < A.Length ==> A[i] <= A[j]
}

predicate is_pivot(A:array<int>, lo:int, hi:int, pivot:int)
  reads A
  requires 0 <= lo <= pivot < hi <= A.Length
{
  (forall i :: lo <= i < pivot ==> A[i] <= A[pivot]) &&
  (forall i :: pivot < i < hi ==> A[pivot] <= A[i])
}

method partition(A:array<int>, lo:int, hi:int) returns (pivot:int)
  requires 0 <= lo < hi <= A.Length
  requires partitioned(A, lo) && partitioned(A, hi)
  ensures 0 <= lo <= pivot < hi
  ensures is_pivot(A, lo, hi, pivot)
  ensures forall k :: (0 <= k < lo || hi <= k < A.Length) ==> old(A[k]) == A[k]
  ensures partitioned(A, lo) && partitioned(A, hi)
  modifies A
{
  pivot := lo;
  var i := lo+1;
  while i < hi
    invariant 0 <= lo <= pivot < i <= hi
    invariant is_pivot(A, lo, i, pivot)
    invariant forall k :: (0 <= k < lo || hi <= k < A.Length) ==> old(A[k]) == A[k]
    invariant partitioned(A, lo) && partitioned(A, hi)
    decreases hi - i
  {
    if A[i] < A[pivot] {
      var j := i-1;
      var tmp := A[i];
      A[i] := A[j];
      while pivot < j
        invariant is_pivot(A, lo, i+1, pivot)
        invariant tmp <= A[pivot]
        invariant forall k :: (0 <= k < lo || hi <= k < A.Length) ==> old(A[k]) == A[k]
        invariant partitioned(A, lo) && partitioned(A, hi)
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
  requires partitioned(A, lo) && partitioned(A, hi)
  ensures sorted_between(A, lo, hi)
  ensures partitioned(A, lo) && partitioned(A, hi)
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
  ensures sorted(A)
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
  var found:bool := binarysearch_iter(A,4);
  print "Found 4: ", found, "\n";
  found := binarysearch_iter(A,3);
  print "Found 3: ", found, "\n";
}
