// Dafny coursework 2024
//
// Authors: John Wickerson
//
// Note: this file is similar to solutions_2024.dfy but it proves a stronger
// (and more intellectually satisfying!) postcondition for naive_solve.

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
ensures forall x :: x in xs <==> x in ys
{
  if (xs == []) {
    ys := [];
  } else {
    assert xs[0] !in xs[1..];
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
  var zs := xs;
  ys := [];
  while (zs != [])
  invariant dupe_free(zs)
  invariant dupe_free(ys)
  invariant forall x :: x in zs ==> x !in ys
  {
    assert zs[0] !in ys;
    ys := ys + [zs[0]];
    zs := zs[1..];
  }
}

// Part (c): concatenating two dupe-free sequences
lemma dupe_free_concat(xs:seq<symbol>, ys:seq<symbol>)
requires dupe_free(xs)
requires dupe_free(ys)
requires forall x :: !(x in xs && x in ys)
ensures dupe_free (xs + ys)
{
  assert forall i :: 0<=i<|xs| ==> xs[i] in xs;
}

// prepending the empty sequence does nothing
lemma empty_concat<T>(xs:seq<T>)
ensures [] + xs == xs
{}

// distributing the "tail" operation over a concatenation
lemma tail_concat (xs:seq<symbol>, ys:seq<symbol>)
requires xs != []
ensures (xs + ys)[1..] == xs[1..] + ys
{}

//////////////////////////////////////////
// TASK 2: Extracting symbols from queries
//////////////////////////////////////////

// remove the given set of symbols from a clause
function remove_symbols_clause(c:clause, xs:set<symbol>) : clause
ensures |remove_symbols_clause(c,xs)| <= |c|
ensures symbols_clause(remove_symbols_clause(c, xs)) == symbols_clause(c) - xs
ensures xs=={} ==> remove_symbols_clause(c, xs) == c
{
  if c == [] then [] else
    var c' := remove_symbols_clause(c[1..], xs);
    if c[0].0 in xs then c' else
      assert symbols_clause([c[0]] + c') == {c[0].0} + symbols_clause(c');
      [c[0]] + c'
}

// remove the given set of symbols from a query
function remove_symbols(q:query, xs:set<symbol>) : query
ensures |remove_symbols(q,xs)| <= |q|
ensures symbols(remove_symbols(q, xs)) == symbols(q) - xs
ensures xs=={} ==> remove_symbols(q,xs) == q
{
  if q == [] then [] else
    [remove_symbols_clause(q[0], xs)] + remove_symbols(q[1..], xs)
}

// removing xs and then ys from a clause is the same as removing xs+ys in one go
lemma remove_symbols_clause_twice(c:clause, xs:set<symbol>, ys:set<symbol>)
ensures remove_symbols_clause(remove_symbols_clause(c,xs), ys) == remove_symbols_clause(c, xs+ys)
{
  if (c != []) {
    remove_symbols_clause_twice(c[1..], xs, ys); 
    if (remove_symbols_clause(c,xs) != []) {
      if (c[0].0 in xs) {
        assert remove_symbols_clause(c,xs) == remove_symbols_clause(c[1..], xs);
      } 
    }
  }
}

// removing xs and then ys from a query is the same as removing xs+ys in one go
lemma remove_symbols_twice(q:query, xs:set<symbol>, ys:set<symbol>)
ensures remove_symbols(remove_symbols(q,xs), ys) == remove_symbols(q, xs+ys)
{
  if (q != []) {
    remove_symbols_twice(q[1..], xs, ys);
    remove_symbols_clause_twice (q[0], xs, ys);
  }
}

// Part (a): extract the sequence of symbols that appear in a clause
function symbol_seq_clause(c:clause) : seq<symbol>
ensures dupe_free(symbol_seq_clause(c))
ensures forall x :: x in symbol_seq_clause(c) <==> x in symbols_clause(c)
decreases |c|
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
decreases |q|
{
  if q == [] then [] else
    var xs := symbols_clause(q[0]);
    var q' := remove_symbols(q[1..], xs);
    dupe_free_concat(symbol_seq_clause(q[0]), symbol_seq(q'));
    symbol_seq_clause(q[0]) + symbol_seq(q')
}

// removing the first symbol from a clause corresponds to removing the head of its symbol sequence
lemma remove_first_symbol_clause (c:clause, x:symbol)
requires c != []
requires c[0].0 == x
requires symbol_seq_clause(c) != []
ensures symbol_seq_clause(remove_symbols_clause(c,{x})) == symbol_seq_clause(c)[1..]
{
  empty_concat(remove_symbols_clause(c[1..], {x}));
}

// removing the first symbol from a query corresponds to removing the head of its symbol sequence
lemma remove_first_symbol_query (q:query)
requires symbol_seq(q) != []
ensures symbol_seq(remove_symbols(q,{symbol_seq(q)[0]})) == symbol_seq(q)[1..]
{
  var x := symbol_seq(q)[0];
  var q' := remove_symbols(q,{x});
  if (q == []) {
    assert false;
  } else if (q[0] == []) {
    assert symbols_clause([]) == {};
  } else {
    assert q != [];
    assert q[0] != [];
    assert q[0][0].0 == x;
    assert symbol_seq(q) != [];
    remove_first_symbol_clause(q[0],x);
    remove_symbols_twice(q[1..], {x}, symbols_clause(q[0]) - {x});
    tail_concat(symbol_seq_clause(q[0]), symbol_seq(remove_symbols(q[1..], symbols_clause(q[0]))));
    assert forall xs : set<symbol>, ys : set<symbol> :: xs <= ys ==> (xs + (ys - xs) == ys);

    calc {
      symbol_seq(remove_symbols(q,{x}));
      == symbol_seq([remove_symbols_clause(q[0], {x})] + remove_symbols(q[1..], {x}));
      == symbol_seq_clause(remove_symbols_clause(q[0], {x})) + symbol_seq(remove_symbols(remove_symbols(q[1..], {x}), symbols_clause(remove_symbols_clause(q[0], {x}))));
      == symbol_seq_clause(remove_symbols_clause(q[0], {x})) + symbol_seq(remove_symbols(remove_symbols(q[1..], {x}), symbols_clause(q[0]) - {x}));
      == symbol_seq_clause(q[0])[1..] + symbol_seq(remove_symbols(remove_symbols(q[1..], {x}), symbols_clause(q[0]) - {x}));
      == symbol_seq_clause(q[0])[1..] + symbol_seq(remove_symbols(q[1..], {x} + (symbols_clause(q[0]) - {x})));
      == symbol_seq_clause(q[0])[1..] + symbol_seq(remove_symbols(q[1..], symbols_clause(q[0])));
      == (symbol_seq_clause(q[0]) + symbol_seq(remove_symbols(q[1..], symbols_clause(q[0]))))[1..];
      == symbol_seq(q)[1..];
    }
  }
}

/////////////////////////////
// TASK 3: Evaluating queries
/////////////////////////////

// evaluate the given clause under the given valuation (imperative version)
method eval_clause(c:clause, r:valuation) 
returns (result: bool)
ensures result == evaluate_clause(c,r)
{
  var i := 0;
  while (i < |c|)
  invariant i <= |c|
  invariant forall j :: 0 <= j < i ==> c[j] !in r.Items
  {
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
  while (i < |q|)
  invariant i <= |q|
  invariant forall j :: 0 <= j < i ==> evaluate_clause(q[j], r)
  {
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
ensures forall r :: r in rs ==> r[x:=b] in map_prepend(x,b,rs)
{
  if rs == [] then [] else
    assert forall r :: r in rs ==> r == rs[0] || r in rs[1..];
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

lemma mk_valuation_cons(x:symbol, xs:seq<symbol>, r:valuation)
requires x in r.Keys
requires r-{x} in mk_valuation_seq(xs)
ensures r in mk_valuation_seq([x] + xs)
{
  if (r[x] == true) {
    assert r == (r-{x})[x:=true];
  } else {
    assert r == (r-{x})[x:=false];
  }
}

// if r provides a truth-value for all (and only) the symbols in q, then mk_valuation_seq will contain r
lemma mk_valuation_seq_contains_all_valuations_helper (q:query, r:valuation)
requires r.Keys == symbols(q)
decreases symbols(q)
ensures r in mk_valuation_seq(symbol_seq(q))
{
  if (symbol_seq(q) == []) {
    assert symbols(q) == {};
    assert r in mk_valuation_seq(symbol_seq(q));
  } else {
    var x := symbol_seq(q)[0];
    var xs := symbol_seq(q)[1..];
    mk_valuation_seq_contains_all_valuations_helper(remove_symbols(q,{x}), r-{x});
    remove_first_symbol_query(q);
    mk_valuation_cons(x,xs,r);
  }
}

// if r provides a truth-value for all (and only) the symbols in q, then mk_valuation_seq will contain r
function /*lemma*/ mk_valuation_seq_contains_all_valuations (q:query, r:valuation) : bool
requires r.Keys == symbols(q)
ensures r in mk_valuation_seq(symbol_seq(q))
ensures mk_valuation_seq_contains_all_valuations(q,r)
{
  mk_valuation_seq_contains_all_valuations_helper(q,r); true
}

// if q cannot be satisfied by any valuation in mk_valuation_seq, then it cannot
// be satisfied by any valuation that defines all (and only) the symbols in q
lemma mk_valuation_seq_suffices(q:query)
requires forall r:valuation :: r in mk_valuation_seq(symbol_seq(q)) ==> !evaluate(q,r)
ensures forall r:valuation :: r.Keys == symbols(q) ==> !evaluate(q,r)
{
  assert (exists r:valuation :: r.Keys == symbols(q) && evaluate(q,r)) ==> (exists r:valuation :: 
    evaluate(q,r) && r.Keys == symbols(q) && 
    mk_valuation_seq_contains_all_valuations(q,r) && 
    r in mk_valuation_seq(symbol_seq(q))
  );
}

// Part (c): a brute-force SAT solver. Given a query, it constructs all possible 
// valuations over the symbols that appear in the query, and then 
// iterates through those valuations until it finds one that works.
method naive_solve (q:query) 
returns (sat:bool, r:valuation)
ensures sat==true ==> evaluate(q,r)
//ensures sat==false ==> forall r:valuation :: r in mk_valuation_seq(symbol_seq(q)) ==> !evaluate(q,r)
ensures sat==false ==> forall r:valuation :: r.Keys == symbols(q) ==> !evaluate(q,r) 
{
  var xs := symbol_seq(q);
  var rs := mk_valuation_seq(xs);
  sat := false;
  var i := 0;
  while (i < |rs|) 
  invariant i <= |rs|
  invariant forall j :: 0 <= j < i ==> !evaluate(q,rs[j])
  {
    sat := eval(q, rs[i]);
    if (sat) {
      return true, rs[i];
    }
    i := i + 1;
  }
  mk_valuation_seq_suffices(q);
  return false, map[];
}

////////////////////////////////////////
// TASK 4: Verifying a simple SAT solver
////////////////////////////////////////

// the "symbols" function distributes over "+"
lemma symbols_append(q1:query, q2:query)
ensures symbols(q1 + q2) == symbols(q1) + symbols(q2)
{
  if (q1 == []) {
    assert [] + q2 == q2;
  } else {
    assert (q1+q2)[1..] == q1[1..] + q2;
  }
}

// This function updates a clause under the valuation x:=b. 
// This means that the literal (x,b) is true. So, if the clause
// contains the literal (x,b), the whole clause is true and can 
// be deleted. Otherwise, all occurrences of (x,!b) can be 
// removed from the clause because those literals are false and 
// cannot contribute to making the clause true.
function update_clause (x:symbol, b:bool, c:clause) : query
ensures symbols(update_clause(x,b,c)) <= symbols_clause(c) - {x}
{
  if ((x,b) in c) then [] else [remove_symbols_clause(c,{x})]
}

// This function updates a query under the valuation x:=b. It
// invokes update_clause on each clause in turn.
function update_query (x:symbol, b:bool, q:query) : query
ensures symbols (update_query (x, b, q)) <= symbols(q) - {x}
{
  if q == [] then [] else
    var q_new := update_clause(x,b,q[0]);
    var q' := update_query(x,b,q[1..]);
    symbols_append(q_new, q');
    q_new + q'
}

// if query q1+q2 is satisfied, then both q1 and q2 are satisfied
lemma evaluate_append(q1:query, q2:query, r:valuation)
ensures evaluate(q1+q2, r) ==> evaluate(q1, r) && evaluate(q2, r)
{
  if (q1 == []) {
    assert [] + q2 == q2;
  } else {
    assert (q1+q2)[1..] == q1[1..] + q2;
    assert (q1+q2)[0] == q1[0];
    evaluate_append(q1[1..], q2, r);
  }
}

// Removing x from a clause does not affect its evaluation under r 
// as long as the clause does not contain the literal (x, r[x])
lemma evaluate_clause_remove_symbols (x:symbol, b:bool, r:valuation, c:clause)
requires x in r.Keys
requires r[x] == b
requires (x,b) !in c
ensures evaluate_clause (remove_symbols_clause (c,{x}), r) == evaluate_clause (c, r)
{}

// Updating a clause under the valuation x:=b is the same as updating 
// the valuation itself and leaving the clause unchanged.
lemma evaluate_update_clause(x:symbol, b:bool, r:valuation, c:clause)
requires x !in r.Keys
ensures evaluate (update_clause(x,b,c), r) == evaluate_clause (c, r[x:=b])
{
  if ((x,b) !in c) {
    evaluate_clause_remove_symbols(x,b,r[x:=b],c);
  }
}

// Updating a query under the valuation x:=b is the same as updating 
// the valuation itself and leaving the query unchanged.
lemma evaluate_update_query(x:symbol, b:bool, r:valuation, q:query)
requires x !in r.Keys
ensures evaluate (update_query (x,b,q), r) == evaluate (q, r[x:=b])
{
  if (q != []) {
    evaluate_append(update_clause(x,b,q[0]), update_query(x,b,q[1..]), r);
    evaluate_update_clause(x,b,r,q[0]);
    evaluate_update_query(x,b,r,q[1..]);
  }
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
decreases symbols(q)
ensures sat==true ==> (evaluate(q,r) && r.Keys <= symbols(q))
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
      evaluate_update_query(x,true,r,q);
      r := r[x:=true];
      return;
    } 
    
    sat, r := simp_solve(update_query(x,false,q));
    if (sat) {
      evaluate_update_query(x,false,r,q);
      r := r[x:=false];
      return;
    }
    forall r:valuation { evaluate_update_query(x, false, r - {x}, q); }
    forall r:valuation { evaluate_update_query(x, true, r - {x}, q); }
    assert forall r:valuation, b:bool {:trigger} :: !evaluate (q, (r - {x})[x:=b]);
    assert forall r:valuation :: (x in r.Keys) ==> !evaluate (q, (r - {x})[x:=r[x]]);
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
