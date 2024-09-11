// Dafny coursework 2023
//
// Authors: John Wickerson

// Task 1: integer square roots

method int_sqrt(n:nat) returns (r:nat)
  ensures r * r <= n < (r+1) * (r+1)
{
  r := 0;
  while (r + 1) * (r + 1) <= n 
    invariant r * r <= n 
  {
    r := r + 1;
  }
}

// Task 2: analogue-to-digital conversion

function bits_to_nat_upto(bs:array<bool>, hi:nat) : nat
  requires hi <= bs.Length
  reads bs
{
  if hi==0 then 0 else 2 * bits_to_nat_upto(bs, hi-1) + (if bs[hi-1] then 1 else 0)
}

function bits_to_nat(bs:array<bool>) : nat
  reads bs
{
  bits_to_nat_upto(bs, bs.Length)
}

lemma zeroes_to_nat_is_zero_helper (bs:array<bool>, hi:nat)
  requires hi <= bs.Length
  requires forall i :: 0 <= i < hi ==> bs[i] == false
  ensures bits_to_nat_upto(bs, hi) == 0
{ 
  if hi == 0 {
    return;
  } else {
    zeroes_to_nat_is_zero_helper(bs, hi-1);
  }
}

lemma zeroes_to_nat_is_zero(bs:array<bool>)
  requires forall i :: 0 <= i < bs.Length ==> bs[i] == false
  ensures bits_to_nat(bs) == 0
{
    zeroes_to_nat_is_zero_helper(bs,bs.Length);
}

method adc(w:nat, input:nat) returns (SAR:array<bool>)
  ensures bits_to_nat(SAR) <= input
  ensures SAR.Length == w
{
  SAR := new bool[w];
  var c := 0;
  while c < SAR.Length
    invariant c <= SAR.Length
    invariant forall i :: 0 <= i < c ==> SAR[i] == false
  {
    SAR[c] := false;
    c := c + 1;
  }
  assert forall i :: 0 <= i < SAR.Length ==> SAR[i] == false;
  zeroes_to_nat_is_zero(SAR);
  assert bits_to_nat(SAR) == 0;
  c := 0;
  while c < SAR.Length
    invariant c <= SAR.Length
    invariant bits_to_nat(SAR) <= input
    invariant forall i :: c <= i < SAR.Length ==> SAR[i] == false
  {
    SAR[c] := true;
    if bits_to_nat(SAR) > input {
      SAR[c] := false;
    }
    c := c+1;
  }
}

// Task 3: stupidsort

predicate sorted_between(A:array<int>, lo:int, hi:int)
  reads A
  requires 0 <= lo <= hi <= A.Length
{
  forall m,n :: lo <= m < n < hi ==> A[m] <= A[n]
}

predicate sorted(A:array<int>)
  reads A
{
  sorted_between(A,0,A.Length)
}

function min (x:int, y:int) : int
{
    if x < y then x else y
}

function min_between(A:array<int>, lo:int, hi:int) : int
  requires 0 <= lo < hi <= A.Length
  reads A
  decreases hi - lo
  ensures forall k :: lo <= k < hi ==> min_between(A,lo,hi) <= A[k]
  ensures exists k :: lo <= k < hi && min_between(A,lo,hi) == A[k]
{
  if lo == hi - 1 then A[lo] else
  min(A[lo], min_between(A, lo+1, hi))
}


method stupidsort_between(A:array<int>, i:int, j:int)
  requires 0 <= i <= j <= A.Length
  ensures sorted_between(A, i, j)
  ensures forall k :: 0 <= k < i || j <= k < A.Length ==> old(A[k]) == A[k]
  ensures i < j ==> old(min_between(A,i,j)) == min_between(A,i,j)
  modifies A
  decreases j - i
{
  if i < j-1  {
    var m := (i + j) / 2;
    stupidsort_between(A, m, j);
    assert m+1<j ==> A[m] <= min_between(A,m+1,j);
    stupidsort_between(A, i, m);
    assert i+1<m ==> A[i] <= min_between(A,i+1,m);
    if A[m] < A[i] {
      A[i], A[m] := A[m], A[i];
    } 
    assert A[i] <= min_between(A,i+1,j);
    stupidsort_between(A, i+1, j);
  } 
}

method stupidsort(A:array<int>)
  ensures sorted(A)
  modifies A
{
  stupidsort_between(A, 0, A.Length);
}

method Main() {
  var r := int_sqrt(15);
  var s := int_sqrt(16);
  print "sqrt(15) = ", r, " and sqrt(16) = ", s, "\n";

  var A:array<int> := new int[7] [4,0,1,9,7,1,2];
  print "Before: ", A[0], A[1], A[2], A[3], 
        A[4], A[5], A[6], "\n";
  stupidsort(A);
  print "After:  ", A[0], A[1], A[2], A[3], 
        A[4], A[5], A[6], "\n";

  var SAR:array<bool> := adc(5,10);
  print "After ADC: [", SAR[0], ",", SAR[1], ",", 
        SAR[2], ",", SAR[3], ",", SAR[4], "]\n";
}
