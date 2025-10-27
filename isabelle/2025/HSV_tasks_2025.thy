theory HSV_tasks_2025 imports Main begin

section \<open> Task 1: Assessing the efficiency of a logic synthesiser. \<close>

text \<open> A datatype representing simple circuits. \<close>

datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

text \<open> An optimisation that removes two successive NOT gates. \<close>

fun opt_NOT where
  "opt_NOT (NOT (NOT c)) = opt_NOT c"
| "opt_NOT (NOT c) = NOT (opt_NOT c)"
| "opt_NOT (AND c1 c2) = AND (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT (OR c1 c2) = OR (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT TRUE = TRUE"
| "opt_NOT FALSE = FALSE"
| "opt_NOT (INPUT i) = INPUT i"

text \<open> A function that counts the number of gates in a circuit. \<close>

fun area :: "circuit \<Rightarrow> nat" where
  "area (NOT c) = 1 + area c"
| "area (AND c1 c2) = 1 + area c1 + area c2"
| "area (OR c1 c2) = 1 + area c1 + area c2"
| "area _ = 0"

text \<open> A function that estimates the computational "cost" of the opt_NOT function. \<close>

fun cost_opt_NOT :: "circuit \<Rightarrow> nat" where
  "cost_opt_NOT (NOT (NOT c)) = 1 + cost_opt_NOT c"
| "cost_opt_NOT (NOT c) = 1 + cost_opt_NOT c"
| "cost_opt_NOT (AND c1 c2) = 1 + cost_opt_NOT c1 + cost_opt_NOT c2"
| "cost_opt_NOT (OR c1 c2) = 1 + cost_opt_NOT c1 + cost_opt_NOT c2"
| "cost_opt_NOT TRUE = 1"
| "cost_opt_NOT FALSE = 1"
| "cost_opt_NOT (INPUT _) = 1"

text \<open> opt_NOT has complexity O(n) where n is the input circuit's area. \<close>

theorem opt_NOT_linear: "\<exists> a b ::nat. cost_opt_NOT c \<le> a * area c + b"
  oops

text \<open> Another optimisation, introduced in the 2021 coursework. This
  optimisation exploits identities like `(a | b) & (a | c) = a | (b & c)` 
  in order to remove some gates. \<close>

fun factorise :: "circuit \<Rightarrow> circuit" where
  "factorise (NOT c) = NOT (factorise c)"
| "factorise (AND (OR c1 c2) (OR c3 c4)) = (
    let c1' = factorise c1; c2' = factorise c2; c3' = factorise c3; c4' = factorise c4 in
    if c1' = c3' then OR c1' (AND c2' c4') 
    else if c1' = c4' then OR c1' (AND c2' c3') 
    else if c2' = c3' then OR c2' (AND c1' c4') 
    else if c2' = c4' then OR c2' (AND c1' c3') 
    else AND (OR c1' c2') (OR c3' c4'))"
| "factorise (AND c1 c2) = AND (factorise c1) (factorise c2)"
| "factorise (OR c1 c2) = OR (factorise c1) (factorise c2)"
| "factorise TRUE = TRUE"
| "factorise FALSE = FALSE"
| "factorise (INPUT i) = INPUT i"

text \<open> A function that estimates the computational "cost" of the factorise function. \<close>

fun cost_factorise :: "circuit \<Rightarrow> nat" where
  "cost_factorise (NOT c) = 1 + cost_factorise c"
| "cost_factorise (AND (OR c1 c2) (OR c3 c4)) = 
   4 + cost_factorise c1 + cost_factorise c2 + cost_factorise c3 + cost_factorise c4"
| "cost_factorise (AND c1 c2) = 1 + cost_factorise c1 + cost_factorise c2"
| "cost_factorise (OR c1 c2) = 1 + cost_factorise c1 + cost_factorise c2"
| "cost_factorise TRUE = 1"
| "cost_factorise FALSE = 1"
| "cost_factorise (INPUT i) = 1"

text \<open> factorise has complexity O(n) where n is the input circuit's area. \<close>

theorem factorise_linear: "\<exists> a b ::nat. cost_factorise c \<le> a * area c + b"
  oops

section \<open> Task 2: Palindromic numbers. \<close>

fun sum10 :: "nat list \<Rightarrow> nat"
where
  "sum10 [] = 0"
| "sum10 (d # ds) = d + 10 * sum10 ds"

value "sum10 [4,2,3]"

text \<open> Rephrasing the definition of sum10 so that elements 
  are peeled off the _end_ of the list, not the start. \<close>

lemma sum10_snoc:
  "sum10 (ds @ [d]) =  ... sum10 ds ... "
  oops

text \<open> If ds is a palindrome of even length, then the number it represents is divisible by 11. \<close>
theorem dvd11: 
  assumes "even (length ds)"
  assumes "ds = rev ds"
  shows "11 dvd (sum10 ds)"
  oops

section \<open> Task 3: 3SAT reduction. \<close>

text \<open> We shall use integers to represent symbols. \<close>
type_synonym symbol = "nat"

text \<open> A literal is either a symbol or a negated symbol. \<close>
type_synonym literal = "symbol * bool"

text \<open> A clause is a disjunction of literals. \<close>
type_synonym clause = "literal list"

text \<open> A SAT query is a conjunction of clauses. \<close>
type_synonym query = "clause list"

text \<open> A valuation is a function from symbols to truth values. \<close>
type_synonym valuation = "symbol \<Rightarrow> bool"

text \<open> Given a valuation, evaluate a literal to its truth value. \<close>
fun evaluate_literal :: "valuation \<Rightarrow> literal \<Rightarrow> bool"
where 
  "evaluate_literal \<rho> (x,b) = (\<rho> x = b)"

text \<open> Given a valuation, evaluate a clause to its truth value. \<close>
definition evaluate_clause :: "valuation \<Rightarrow> clause \<Rightarrow> bool"
where 
  "evaluate_clause \<rho> c \<equiv> \<exists>l \<in> set c. evaluate_literal \<rho> l"

text \<open> Given a valuation, evaluate a query to its truth value. \<close>
definition evaluate :: "query \<Rightarrow> valuation \<Rightarrow> bool"
where 
  "evaluate q \<rho> \<equiv> \<forall>c \<in> set q. evaluate_clause \<rho> c"

text \<open> Checks whether a query is in 3SAT form; i.e. no clause has more than 3 literals. \<close>
definition is_3SAT :: "query \<Rightarrow> bool"
where[simp]:
  "is_3SAT q \<equiv> \<forall>c \<in> set q. length c \<le> 3"

text \<open> Converts a clause into an equivalent sequence of 3SAT clauses. The 
       parameter x is the next symbol number to use whenever a fresh symbol 
       is required. It should be greater than every symbol that appears in c.
       When the function returns, it returns a new value for this parameter
       that may have been increased as a result of adding new symbols; the 
       function guarantees that the new value is still greater than every
       symbol that appears in sequence of reduced clauses. \<close>

fun reduce_clause :: "symbol \<Rightarrow> clause \<Rightarrow> (symbol * query)"
where
  "reduce_clause x (l1 # l2 # l3 # l4 # c) = 
  (let (x',cs) = reduce_clause (x+1) ((x, False) # l3 # l4 # c) in
  (x', [[(x, True), l1, l2]] @ cs))"
| "reduce_clause x c = (x, [c])"

value "reduce_clause 3 [(0, True), (1, False), (2, True)]"
value "reduce_clause 4 [(0, True), (1, False), (2, True), (3, False)]"
value "reduce_clause 5 [(0, True), (1, False), (2, True), (3, False), (4, True)]"

text \<open> Converts a SAT query into a 3SAT query. The parameter x is the next
       symbol number to use whenever a fresh symbol is required. It should
       be greater than every symbol that appears in q. We shall sometimes
       write "reduction of q at x". \<close>
fun reduce :: "symbol \<Rightarrow> query \<Rightarrow> query"
where
  "reduce _ [] = []"
| "reduce x (c # q) = (let (x',cs) = reduce_clause x c in cs @ reduce x' q)"

text \<open> "x \<triangleright> q" holds if all the symbols in q are below x.  \<close>
definition all_below :: "nat \<Rightarrow> query \<Rightarrow> bool" (infix "\<triangleright>" 50)
where [simp]:
  "x \<triangleright> q \<equiv> \<forall>c \<in> set q. \<forall>(y,_) \<in> set c. y<x"

definition "q_example \<equiv> [[(0,True), (1,True), (2,True), (3,False)], [(1,False), (2,True)]]"

value "3 \<triangleright> q_example"
value "4 \<triangleright> q_example"

value "reduce 4 q_example"

text \<open> The constant-False valuation satisfies q_example... \<close>
value "evaluate q_example (\<lambda>_. False)"

text \<open> ...but it doesn't satisfy the reduced version of q_example. \<close>
value "evaluate (reduce 4 q_example) (\<lambda>_. False)"

text \<open> Extract the symbol from a given literal. \<close>
fun symbol_of_literal :: "literal \<Rightarrow> symbol"
where
  "symbol_of_literal (x, _) = x"

text \<open> Extract the set of symbols that appear in a given clause. \<close>
definition symbols_clause :: "clause \<Rightarrow> symbol set"
where 
  "symbols_clause c \<equiv> set (map symbol_of_literal c)"

text \<open> Extract the set of symbols that appear in a given query. \<close>
definition symbols :: "query \<Rightarrow> symbol set"
where
  "symbols q \<equiv> \<Union> (set (map symbols_clause q))"


text \<open> The reduce function really does return queries in 3SAT form. \<close>
theorem is_3SAT_reduce:
  "is_3SAT (reduce x q)" 
  oops


text \<open> The reduce function never decreases the number of clauses in a query. \<close>
theorem "length q \<le> length (reduce x q)"
  oops

definition "satisfiable q \<equiv> \<exists>\<rho>. evaluate q \<rho>"

text \<open> If reduce x q is satisfiable, then so is q. \<close>
theorem sat_reduce1:
  assumes "satisfiable (reduce x q)"
  shows "satisfiable q"
  sorry

text \<open> If q is satisfiable, and all the symbols in q are below x, 
  then reduce x q is also satisfiable. \<close>
theorem sat_reduce2:
  assumes "satisfiable q" and "x \<triangleright> q"
  shows "satisfiable (reduce x q)"
  sorry

text \<open> If all symbols in q are below x, then q and its reduction at x are equisatisfiable. \<close>
corollary sat_reduce:
  assumes "x \<triangleright> q"
  shows "satisfiable q = satisfiable (reduce x q)"
  using assms sat_reduce1 sat_reduce2 by blast

end