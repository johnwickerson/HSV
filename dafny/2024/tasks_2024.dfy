// Dafny coursework 2024
//
// Authors: John Wickerson
//
// Changelog:
// * 5-Nov: "Task 5" was mis-labelled as "Task 4" below; now fixed.

type symbol = int
type literal = (symbol,bool)
type clause = seq<literal>
type query = seq<clause>
type valuation = map<symbol,bool>

// extracts the set of symbols from a given clause
function symbols_clause(c:clause) : set<symbol>
ensures (forall xb :: xb in c ==> xb.0 in symbols_clause(c))
ensures (forall x :: (x in symbols_clause(c)) ==> (exists b :: (x,b) in c))
{
  if c == [] then {} else 
    assert forall xb :: xb in c ==> xb in {c[0]} || xb in c[1..];
    {c[0].0} + symbols_clause(c[1..])
}

// extracts the set of symbols from a given query
function symbols(q:query) : set<symbol>
{
  if q == [] then {} else
    symbols(q[1..]) + symbols_clause(q[0])
}

// evaluates the given clause under the given valuation
predicate evaluate_clause(c:clause, r:valuation) {
  exists xb :: (xb in c) && (xb in r.Items)
}

// evaluates the given query under the given valuation
predicate evaluate(q:query, r:valuation) {
  forall i :: 0 <= i < |q| ==> evaluate_clause(q[i], r)
}

///////////////////////////////////
// TASK 1: Duplicate-free sequences
///////////////////////////////////

// holds if a sequence of symbols has no duplicates
predicate dupe_free(xs:seq<symbol>) 
{
  forall i,j :: 0 <= i < j < |xs| ==> xs[i] != xs[j]
}

// Part (a): reversing a dupe-free sequence (recursive implementation)
method rev(xs:seq<symbol>)
returns (ys:seq<symbol>)
requires dupe_free(xs)
ensures dupe_free(ys)
{
  if (xs == []) {
    ys := [];
  } else {
    ys := rev(xs[1..]);
    ys := ys + [xs[0]];
  }
}

// Part (b): reversing a dupe-free sequence (iterative implementation)
method rev2(xs:seq<symbol>)
returns (ys:seq<symbol>)
requires dupe_free(xs)
ensures dupe_free(ys)
{
  // ...?
}

// Part (c): concatenating two dupe-free sequences
lemma dupe_free_concat(xs:seq<symbol>, ys:seq<symbol>)
requires dupe_free(xs)
requires dupe_free(ys)
//requires ...?
ensures dupe_free (xs + ys)
{
  // ...?
}

//////////////////////////////////////////
// TASK 2: Extracting symbols from queries
//////////////////////////////////////////

// remove the given set of symbols from a clause
function remove_symbols_clause(c:clause, xs:set<symbol>) : clause
ensures symbols_clause(remove_symbols_clause(c, xs)) == symbols_clause(c) - xs
{
  if c == [] then [] else
    var c' := remove_symbols_clause(c[1..], xs);
    if c[0].0 in xs then c' else [c[0]] + c'
}

// remove the given set of symbols from a query
function remove_symbols(q:query, xs:set<symbol>) : query
ensures symbols(remove_symbols(q, xs)) == symbols(q) - xs
{
  if q == [] then [] else
    [remove_symbols_clause(q[0], xs)] + remove_symbols(q[1..], xs)
}

// Part (a): extract the sequence of symbols that appear in a clause
function symbol_seq_clause(c:clause) : seq<symbol>
ensures dupe_free(symbol_seq_clause(c))
ensures forall x :: x in symbol_seq_clause(c) <==> x in symbols_clause(c)
{
  if c == [] then [] else
    var x := c[0].0;
    var c' := remove_symbols_clause(c[1..], {x});
    [x] + symbol_seq_clause(c')
}

// Part (b): extract the sequence of symbols that appear in a query
function symbol_seq(q:query) : seq<symbol>
ensures dupe_free(symbol_seq(q))
ensures forall x :: x in symbol_seq(q) <==> x in symbols(q)
{
  if q == [] then [] else
    var xs := symbols_clause(q[0]);
    var q' := remove_symbols(q[1..], xs);
    symbol_seq_clause(q[0]) + symbol_seq(q')
}

/////////////////////////////
// TASK 3: Evaluating queries
/////////////////////////////

// evaluate the given clause under the given valuation (imperative version)
method eval_clause (c:clause, r:valuation) 
returns (result: bool)
ensures result == evaluate_clause(c,r)
{
  var i := 0;
  while (i < |c|) {
    if (c[i] in r.Items) {
      return true;
    }
    i := i + 1;
  }
  return false;
}

// evaluate the given query under the given valuation (imperative version)
method eval(q:query, r:valuation) 
returns (result: bool)
ensures result == evaluate(q,r)
{
  var i := 0;
  while (i < |q|) {
    result := eval_clause(q[i], r);
    if (!result) {
      return false;
    }
    i := i + 1;
  }
  return true;
}

/////////////////////////////////////////////
// TASK 4: Verifying a brute-force SAT solver
/////////////////////////////////////////////

// prepends (x,b) to each valuation in a given sequence 
function map_prepend (x:symbol, b:bool, rs:seq<valuation>) : seq<valuation>
{
  if rs == [] then [] else
    [rs[0][x:=b]] + map_prepend(x,b,rs[1..])
}

// constructs all possible valuations of the given symbols
function mk_valuation_seq (xs: seq<symbol>) : seq<valuation>
{
  if xs == [] then [ map[] ] else
    var rs := mk_valuation_seq(xs[1..]);
    var x := xs[0];
    map_prepend(x,true,rs) + map_prepend(x,false,rs)
}

// Part (c): a brute-force SAT solver. Given a query, it constructs all possible 
// valuations over the symbols that appear in the query, and then 
// iterates through those valuations until it finds one that works.
method naive_solve (q:query) 
returns (sat:bool, r:valuation)
ensures sat==true ==> evaluate(q,r)
ensures sat==false ==> forall r:valuation :: r in mk_valuation_seq(symbol_seq(q)) ==> !evaluate(q,r)
{
  var xs := symbol_seq(q);
  var rs := mk_valuation_seq(xs);
  sat := false;
  var i := 0;
  while (i < |rs|) 
  {
    sat := eval(q, rs[i]);
    if (sat) {
      return true, rs[i];
    }
    i := i + 1;
  }
  return false, map[];
}

////////////////////////////////////////
// TASK 5: Verifying a simple SAT solver
////////////////////////////////////////

// This function updates a clause under the valuation x:=b. 
// This means that the literal (x,b) is true. So, if the clause
// contains the literal (x,b), the whole clause is true and can 
// be deleted. Otherwise, all occurrences of (x,!b) can be 
// removed from the clause because those literals are false and 
// cannot contribute to making the clause true.
function update_clause (x:symbol, b:bool, c:clause) : query
{
  if ((x,b) in c) then [] else [remove_symbols_clause(c,{x})]
}

// This function updates a query under the valuation x:=b. It
// invokes update_clause on each clause in turn.
function update_query (x:symbol, b:bool, q:query) : query
{
  if q == [] then [] else
    var q_new := update_clause(x,b,q[0]);
    var q' := update_query(x,b,q[1..]);
    q_new + q'
}

// Updating a query under the valuation x:=b is the same as updating 
// the valuation itself and leaving the query unchanged.
lemma evaluate_update_query(x:symbol, b:bool, r:valuation, q:query)
requires x !in r.Keys
ensures evaluate (update_query (x,b,q), r) == evaluate (q, r[x:=b])
{
  // ...?
}

// A simple SAT solver. Given a query, it does a three-way case split. If
// the query has no clauses then it is trivially satisfiable (with the
// empty valuation). If the first clause in the query is empty, then the
// query is unsatisfiable. Otherwise, it considers the first symbol that 
// appears in the query, and makes two recursive solving attempts: one 
// with that symbol evaluated to true, and one with it evaluated to false.
// If neither recursive attempt succeeds, the query is unsatisfiable.
method simp_solve (q:query)
returns (sat:bool, r:valuation)
ensures sat==true ==> evaluate(q,r)
ensures sat==false ==> forall r :: !evaluate(q,r)
{
  if (q == []) {
    return true, map[];
  } else if (q[0] == []) {
    return false, map[];
  } else {
    var x := q[0][0].0;
    sat, r := simp_solve(update_query(x,true,q));
    if (sat) {
      r := r[x:=true];
      return;
    } 
    sat, r := simp_solve(update_query(x,false,q));
    if (sat) {
      r := r[x:=false];
      return;
    }
    return sat, map[];
  }
}

method Main ()
{
  var sat : bool;
  var r : valuation;
  var q1 := /* (a ∨ b) ∧ (¬b ∨ c) */ 
            [[(1, true), (2, true)], [(2, false), (3, true)]];
  var q2 := /* (a ∨ b) ∧ (¬a ∨ ¬b) */
            [[(1, true), (2, true)], [(1, false)], [(2, false)]];
  var q3 := /* (a ∨ ¬b) */
            [[(1, true), (2, false)]];
  var q4 := /* (¬b ∨ a) */
            [[(2, false), (1, true)]];
  
  var symbol_seq := symbol_seq(q1);
  print "symbols = ", symbol_seq, "\n";

  var rs := mk_valuation_seq(symbol_seq);
  print "all valuations = ", rs, "\n";
  
  sat, r := naive_solve(q1);
  print "solver = naive, q1 result = ", sat, ", valuation = ", r, "\n";

  sat, r := naive_solve(q2);
  print "solver = naive, q2 result = ", sat, ", valuation = ", r, "\n";

  sat, r := naive_solve(q3);
  print "solver = naive, q3 result = ", sat, ", valuation = ", r, "\n";

  sat, r := naive_solve(q4);
  print "solver = naive, q4 result = ", sat, ", valuation = ", r, "\n";

  sat, r := simp_solve(q1);
  print "solver = simp, q1 result = ", sat, ", valuation = ", r, "\n";

  sat, r := simp_solve(q2);
  print "solver = simp, q2 result = ", sat, ", valuation = ", r, "\n";

  sat, r := simp_solve(q3);
  print "solver = simp, q3 result = ", sat, ", valuation = ", r, "\n";

  sat, r := simp_solve(q4);
  print "solver = simp, q4 result = ", sat, ", valuation = ", r, "\n";
}
