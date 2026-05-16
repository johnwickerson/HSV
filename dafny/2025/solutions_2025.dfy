// Dafny coursework 2025 (solutions)
//
// Authors: John Wickerson

predicate sorted_between(A:array<int>, lo:int, hi:int)
  reads A
  requires 0 <= lo <= hi <= A.Length
{
  forall m,n :: lo <= m < n < hi ==> A[m] <= A[n]
}

predicate sorted(A:array<int>)
  reads A
{
  sorted_between(A, 0, A.Length)
}

function min (m:int, n:int) : int
  ensures min(m, n) == m || min(m, n) == n
  ensures min(m, n) <= m
  ensures min(m, n) <= n
{
  if m < n then m else n
}

function max (m:int, n:int) : int
  ensures max(m, n) == m || max(m, n) == n
  ensures m <= max(m, n)
  ensures n <= max(m, n)
{
  if m < n then n else m
}

function min_between (A:array<int>, lo:int, hi:int) : int
  requires 0 <= lo < hi <= A.Length
  ensures exists i :: lo <= i < hi && min_between(A, lo, hi) == A[i]
  ensures forall i :: lo <= i < hi ==> min_between(A, lo, hi) <= A[i]
  reads A
  decreases A.Length - lo
{
  if lo == hi - 1 then
    A[lo]
  else
    min (A[lo], min_between (A, lo + 1, hi))
}

function max_between (A:array<int>, lo:int, hi:int) : int
  requires 0 <= lo < hi <= A.Length
  ensures exists i :: lo <= i < hi && max_between(A, lo, hi) == A[i]
  ensures forall i :: lo <= i < hi ==> A[i] <= max_between(A, lo, hi)
  reads A
  decreases A.Length - lo
{
  if lo == hi - 1 then
    A[lo]
  else
    max (A[lo], max_between (A, lo + 1, hi))
}

method sort_pair(A:array<int>, lo:int, hi:int) 
  requires 0 <= lo < hi < A.Length
  ensures forall i :: 0 <= i < A.Length && i!=lo && i!=hi ==> old(A[i]) == A[i]
  ensures A[lo] == old(min(A[lo], A[hi]))
  ensures A[hi] == old(max(A[lo], A[hi]))
  modifies A
{
  if A[hi] < A[lo] {
    A[lo], A[hi] := A[hi], A[lo];
  } 
}

method doublesort_from_to(A:array<int>, lo:int, hi:int)
  requires 0 <= lo <= hi <= A.Length
  ensures lo < hi ==> old(min_between(A, lo, hi)) == min_between(A, lo, hi)
  ensures lo < hi ==> old(max_between(A, lo, hi)) == max_between(A, lo, hi)
  ensures sorted_between(A, lo, hi) 
  ensures forall i :: 0 <= i < lo ==> old(A[i]) == A[i]
  ensures forall i :: hi <= i < A.Length ==> old(A[i]) == A[i]
  modifies A
  decreases hi - lo
{
  if lo + 1 < hi {
    doublesort_from_to(A, lo + 1, hi - 1);
    sort_pair(A, lo, hi - 1);
    sort_pair(A, hi - 2, hi - 1);
    sort_pair(A, lo, lo + 1);
    doublesort_from_to(A, lo + 1, hi - 1);
  }
}

method doublesort_to(A:array<int>, hi:int)
  requires 0 <= hi <= A.Length
  ensures 0 < hi ==> old(max_between(A, 0, hi)) == max_between(A, 0, hi)
  ensures sorted_between(A, 0, hi) 
  ensures forall i :: hi <= i < A.Length ==> old(A[i]) == A[i]
  modifies A
  decreases hi
{
  if 1 < hi {
    doublesort_to(A, hi - 1);
    
    //sort_pair(A, hi - 2, hi - 1);
    if A[hi - 1] < A[hi - 2] {
      A[hi - 2], A[hi - 1] := A[hi - 1], A[hi - 2];
    } 

    doublesort_to(A, hi - 1);
  }
}

method doublesort_from(A:array<int>, lo:int)
  requires 0 <= lo <= A.Length
  ensures lo < A.Length ==> old(min_between(A, lo, A.Length)) == min_between(A, lo, A.Length)
  ensures sorted_between(A, lo, A.Length) 
  ensures forall i :: 0 <= i < lo ==> old(A[i]) == A[i]
  modifies A
  decreases A.Length - lo
{
  if lo + 1 < A.Length {
    doublesort_from(A, lo + 1);

    //sort_pair(A, lo, lo + 1);
    if A[lo + 1] < A[lo] {
      A[lo], A[lo + 1] := A[lo + 1], A[lo];
    } 
    
    doublesort_from(A, lo + 1);
  }
}

method doublesort(A:array<int>)
  ensures sorted(A)
  modifies A 
{
  doublesort_from(A, 0);
  doublesort_to(A, A.Length);
  doublesort_from_to(A, 0, A.Length);
}

method Main() {
  var A:array<int> := new int[7] [4,0,1,9,7,1,2];
  print "Before: ", A[0], A[1], A[2], A[3], 
        A[4], A[5], A[6], "\n";
  doublesort(A);
  print "After:  ", A[0], A[1], A[2], A[3], 
        A[4], A[5], A[6], "\n";
}
