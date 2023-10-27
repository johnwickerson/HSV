// Dafny coursework 2023
//
// Authors: John Wickerson

/////////////////////////////////////////////////////
// Task 1: integer square roots

method int_sqrt(n:nat) returns (r:nat)
  ensures // todo
{
  // todo
} 

/////////////////////////////////////////////////////
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

method adc(w:nat, input:nat) returns (SAR:array<bool>)
  ensures bits_to_nat(SAR) <= input
  ensures SAR.Length == w
{
  SAR := new bool[w];
  var c := 0;
  while c < SAR.Length {
    SAR[c] := false;
    c := c + 1;
  }
  c := 0;
  while c < SAR.Length {
    SAR[c] := true;
    if bits_to_nat(SAR) > input {
      SAR[c] := false;
    }
    c := c+1;
  }
}

/////////////////////////////////////////////////////
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

method stupidsort_between(A:array<int>, i:int, j:int)
{
  if i < j-1  {
    var m := (i + j) / 2;
    stupidsort_between(A, m, j);
    stupidsort_between(A, i, m);
    if A[m] < A[i] {
      A[i], A[m] := A[m], A[i];
    } 
    stupidsort_between(A, i+1, j);
  } 
}

method stupidsort(A:array<int>)
  ensures sorted(A)
{
  stupidsort_between(A, 0, A.Length);
}

/////////////////////////////////////////////////////

method Main() 
{
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