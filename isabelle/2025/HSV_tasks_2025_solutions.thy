theory HSV_tasks_2025_solutions imports Main begin

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
  apply (rule exI[of _ 2])
  apply (rule exI[of _ 1])
  apply (induct rule: cost_opt_NOT.induct)
  apply simp+
  done

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
  apply (rule exI[of _ 3])
  apply (rule exI[of _ 1])
  apply (induct rule: cost_factorise.induct)
  apply simp+
  done

section \<open> Task 2: Palindromic numbers. \<close>

fun sum10 :: "nat list \<Rightarrow> nat"
where
  "sum10 [] = 0"
| "sum10 (d # ds) = d + 10 * sum10 ds"

value "sum10 [4,2,3]"

text \<open> Rephrasing the definition of sum10 so that elements 
  are peeled off the _end_ of the list, not the start. \<close>

lemma sum10_snoc:
  "sum10 (ds @ [d]) = sum10 ds + 10^(length ds) * d"
by (induct ds, auto)

lemma rev_cons_snoc:
  "rev(x # xs @ [x']) = y # ys @ [y'] \<Longrightarrow> x = y' \<and> rev xs = ys \<and> x' = y"
by simp

text \<open> If a list has at least two elements, it must have a first element and a last element. \<close>

lemma extract_head_and_last:
  assumes "2 \<le> length xs"
  shows "\<exists>x y xs'. xs = x # xs' @ [y]"
proof (cases xs)
  case Nil
  thus ?thesis using assms by auto
next
  case (Cons x xs'')
  then show ?thesis 
  proof (cases xs'' rule: rev_cases)
    case Nil
    thus ?thesis using assms Cons by simp
  next
    case (snoc xs' y)
    thus ?thesis using Cons by simp
  qed
qed

text \<open> 11 divides all numbers in the sequence 11, 1001, 100001, 10000001, ... \<close>

lemma dvd11_1z1: "(11::nat) dvd (1 + 10 ^ (2*n + 1))"
proof (induct n)
  case (Suc n)
  hence "(11::nat) dvd 100 * (1 + 10^(2*n + 1)) - 99" by fastforce
  thus ?case by auto
qed (simp)

text \<open> Rephrasing the dvd11 theorem ready for proof-by-induction. \<close>

lemma dvd11_helper: "length ds = 2 * n \<Longrightarrow> ds = rev ds \<Longrightarrow> 11 dvd (sum10 ds)"
proof (induct n arbitrary: ds)
  case (Suc n)
  hence len_ds: "length ds = 2 * Suc n" and ds_rev: "ds = rev ds" by blast+
  hence "length ds \<ge> 2" by simp
  then obtain d ds' d' where ds_def: "ds = d # ds' @ [d']" 
    using extract_head_and_last by blast

  hence "d = d'" and ds'_rev: "ds' = rev ds'" by (metis ds_rev rev_cons_snoc)+
  have len_ds': "length ds' = 2 * n" using len_ds ds_def by auto

  have "11 dvd d * (1 + 10^(1 + length ds')) + 10 * sum10 ds'" 
    using Suc.hyps[OF len_ds' ds'_rev] len_ds' dvd11_1z1[of n] by fastforce
  moreover have "sum10 (d # ds' @ [d]) = d * (1 + 10^(1 + length ds')) + 10 * sum10 ds'" 
    using sum10_snoc by simp
  ultimately have "11 dvd sum10 (d # ds' @ [d'])" using `d = d'` by argo 
  thus ?case using ds_def by simp
qed (auto)

text \<open> If ds is a palindrome of even length, then the number it represents is divisible by 11. \<close>
theorem dvd11: 
  assumes "even (length ds)"
  assumes "ds = rev ds"
  shows "11 dvd (sum10 ds)"
  using assms dvd11_helper by fastforce

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

text \<open> The reduce_clause function really does return queries in 3SAT form. \<close>
lemma is_3SAT_reduce_clause: 
  "is_3SAT (snd (reduce_clause x c))" 
proof (induct rule: reduce_clause.induct)
  case (1 x l1 l2 l3 l4 c)
  thus ?case by (cases "reduce_clause (Suc x) ((x, False) # l3 # l4 # c)", simp)
qed simp+

text \<open> The reduce function really does return queries in 3SAT form. \<close>
theorem is_3SAT_reduce:
  "is_3SAT (reduce x q)" 
proof (induct q arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons a q)
  thus ?case 
    apply (cases "reduce_clause x a")
    apply simp
    apply (metis is_3SAT_def is_3SAT_reduce_clause prod.sel(2) UnE)
    done
qed

text \<open> The reduce_clause function always returns a query containing at least one clause. \<close>

lemma reduce_clause_nonempty: 
  "1 \<le> length (snd (reduce_clause x c))" 
proof (cases c)
  case Nil
  thus ?thesis by simp
next
  case (Cons l1 c1)
  note c_def = this
  show ?thesis
  proof (cases c1)
    case Nil
    thus ?thesis by (simp add: c_def)
  next
    case (Cons l2 c2)
    note c1_def = this
    show ?thesis
    proof (cases c2)
      case Nil
      thus ?thesis by (simp add: c_def c1_def)
    next
      case (Cons l3 c3)
      note c2_def = this
      show ?thesis
      proof (cases c3)
        case Nil
        thus ?thesis by (simp add: c_def c1_def c2_def)
      next
        case (Cons l4 c4)
        thus ?thesis
          apply (case_tac "reduce_clause (Suc x) ((x, False) # l3 # l4 # c4)")
          apply (simp add: c_def c1_def c2_def)
          done
      qed
    qed
  qed
qed

text \<open> The reduce function never decreases the number of clauses in a query. \<close>

theorem "length q \<le> length (reduce x q)"
proof (induct q arbitrary: x)
  case Nil
  thus ?case by simp
next
  case (Cons c q)
  show ?case 
    apply (cases "reduce_clause x c")
    using reduce_clause_nonempty[of x c] 
    using Cons[of "fst(reduce_clause x c)"]
    by simp
qed

text \<open> If \<rho> satisfies the reduction of c, then \<rho> satisfies c. \<close>
lemma equiv_reduce_clause1:
  assumes "evaluate (snd (reduce_clause x c)) \<rho>"
  shows "evaluate [c] \<rho>"
using assms 
proof (induct rule: reduce_clause.induct)
  case (1 x l1 l2 l3 l4 c)
  then obtain x' cs where 
    "reduce_clause (x + 1) ((x, False) # l3 # l4 # c) = (x',cs)" 
    and second_clause_sat: "evaluate_clause \<rho> ((x, False) # l3 # l4 # c)" 
    and first_clause_sat: "evaluate_clause \<rho> [(x, True), l1, l2]"
    by (cases "reduce_clause (x + 1) ((x, False) # l3 # l4 # c)", simp add: evaluate_def)
  {
    assume "\<not> evaluate_clause \<rho> [l3, l4]"
    moreover
    assume "\<not> evaluate_clause \<rho> [l1, l2]"
    hence "\<rho> x" using first_clause_sat 
      by (simp add: in_set_member evaluate_clause_def)
    ultimately
    have "evaluate_clause \<rho> c" using second_clause_sat 
      by (simp add: in_set_member evaluate_clause_def)
  }
  thus "evaluate [l1 # l2 # l3 # l4 # c] \<rho>" using evaluate_def evaluate_clause_def by auto
qed (simp add: evaluate_def)+

text \<open> If \<rho> satisfies the reduction of q at x, then \<rho> satisfies q. \<close>
lemma equiv_reduce1:
  assumes "evaluate (reduce x q) \<rho>"
  shows "evaluate q \<rho>"
using assms 
proof (induct q arbitrary: x)
  case Nil
  thus ?case by simp
next
  case (Cons c q)

  then obtain x' cs where 
    r: "reduce_clause x c = (x', cs)" and "evaluate (cs @ reduce x' q) \<rho>" 
    by (cases "reduce_clause x c", auto)

  hence e: "evaluate cs \<rho>" and "evaluate (reduce x' q) \<rho>" 
    using evaluate_def by simp+

  hence "evaluate q \<rho>" using Cons.hyps by blast

  moreover have "evaluate_clause \<rho> c" using r e equiv_reduce_clause1 evaluate_def 
    by (metis snd_conv list.set_intros(1))

  ultimately show ?case using evaluate_def by auto
qed

definition "satisfiable q \<equiv> \<exists>\<rho>. evaluate q \<rho>"

text \<open> If reduce x q is satisfiable, then so is q. \<close>
theorem sat_reduce1:
  assumes "satisfiable (reduce x q)"
  shows "satisfiable q"
  using assms equiv_reduce1 satisfiable_def by blast

text \<open> Two functions agreeing on the first n numbers. \<close>
definition agree_upto 
  where [simp]: "agree_upto n f g \<equiv> \<forall>m<n. f m = g m"

text \<open> If \<rho> and \<rho>' agree on all the symbols in c, then \<rho> satisfies c iff \<rho>' satisfies c. \<close>
lemma evaluate_clause_irrelevant_symbols:
  assumes "\<forall>x \<in> symbols_clause c. \<rho> x = \<rho>' x"
  shows "evaluate_clause \<rho> c = evaluate_clause \<rho>' c"
  using assms
  by (induct c, auto simp add: evaluate_clause_def symbols_clause_def)

text \<open> If \<rho> and \<rho>' agree on all the symbols in q, then they equally satisfy q. \<close>
lemma evaluate_irrelevant_symbols:
  assumes "\<forall>x \<in> symbols q. \<rho> x = \<rho>' x"
  shows "evaluate q \<rho> = evaluate q \<rho>'"
  using assms
proof (induct q)
  case Nil
  thus ?case using evaluate_def by simp
next
  case (Cons c q)
  hence "\<forall>x \<in> symbols q. \<rho> x = \<rho>' x" and "\<forall>x \<in> symbols_clause c. \<rho> x = \<rho>' x" 
    using symbols_def by simp+
  with evaluate_clause_irrelevant_symbols show ?case using Cons.hyps evaluate_def by auto
qed

text \<open> If all symbols in c are below x, then no symbol greater than or equal to x appears in c. \<close>
lemma all_below_notin_symbols_clause:
  "x \<triangleright> [c] \<Longrightarrow> x \<le> y \<Longrightarrow> y \<notin> symbols_clause c"
by (induct c, auto simp add: symbols_clause_def)

text \<open> If all symbols in q are below x, then no symbol greater than or equal to x appears in q. \<close>
lemma all_below_notin_symbols: 
  "x \<triangleright> q \<Longrightarrow> x \<le> y \<Longrightarrow> y \<notin> symbols q"
proof (induct q)
  case Nil
  thus ?case using symbols_def by simp
next
  case Cons
  thus ?case using all_below_notin_symbols_clause symbols_def by auto
qed

text \<open> If all symbols in q are below x, and \<rho> and \<rho>' agree up to x, then they equally satisfy q. \<close>
lemma switch_valuation:
  assumes "agree_upto x \<rho> \<rho>'"
  assumes "x \<triangleright> q"
  shows "evaluate q \<rho> = evaluate q \<rho>'"
by (metis evaluate_irrelevant_symbols assms agree_upto_def leI all_below_notin_symbols)

text \<open> The `reduce_clause` function only ever increases the "next symbol". \<close>
lemma reduce_clause_mono:
  assumes "reduce_clause x c = (x', cs)"
  shows "x \<le> x'"
  using assms
proof (induct arbitrary: x' cs rule: reduce_clause.induct)
  case (1 x l1 l2 l3 l4 c)
  thus ?case by (cases "reduce_clause (x + 1) ((x, False) # l3 # l4 # c)", auto)
qed(simp+)

text \<open> Suppose reducing c at x results in (x',cs). If all symbols in c are below x, then
       all symbols in cs will be below x'. \<close>
lemma reduce_clause_all_below:
  assumes "reduce_clause x c = (x', cs)"
  assumes "x \<triangleright> [c]"
  shows "x' \<triangleright> cs"
  using assms
proof (induct arbitrary: x' cs rule: reduce_clause.induct)
  case (1 x l1 l2 l3 l4 c)

  from "1.prems"(1) obtain cs' where 
    r: "reduce_clause (x + 1) ((x, False) # l3 # l4 # c) = (x', cs')" and 
    cs_def: "cs = [(x, True), l1, l2] # cs'" 
    by (cases "reduce_clause (x + 1) ((x, False) # l3 # l4 # c)", auto)

  have "x \<triangleright> [[l1, l2]]" and "(x + 1) \<triangleright> [l3 # l4 # c]" 
    using "1.prems"(2) by auto

  hence "x' \<triangleright> [[(x, True)]]" and "x' \<triangleright> [[l1, l2]]" and "x' \<triangleright> cs'" 
    using reduce_clause_mono[OF r] and "1.hyps"[OF r] by auto

  thus ?case using cs_def reduce_clause_mono by auto 

qed(simp+)

text \<open> If all symbols in c are below x and \<rho> satisfies c, then there will exist a
       \<rho>' that agrees with \<rho> up to x and that satisfies the reduction of c at x. \<close>
lemma equiv_agree_reduce_clause2:
  assumes "x \<triangleright> [c]"
  assumes "evaluate [c] \<rho>"
  shows "\<exists>\<rho>'. evaluate (snd (reduce_clause x c)) \<rho>' \<and> agree_upto x \<rho>' \<rho>"
  using assms
proof (induct arbitrary: \<rho> rule: reduce_clause.induct)
  case (1 x l1 l2 l3 l4 c \<rho>)
  hence
    w1: "(x + 1) \<triangleright> [[(x, True), l1, l2]]" and 
    w2: "(x + 1) \<triangleright> [(x, False) # l3 # l4 # c]" by auto

  {
    assume "evaluate_clause \<rho> [l1, l2]" 

    moreover have "x \<notin> symbols_clause [l1, l2]" 
      using all_below_notin_symbols_clause "1.prems"(1) by auto

    ultimately have "evaluate_clause (\<rho>(x:=False)) [l1, l2]" 
      by (metis fun_upd_other evaluate_clause_irrelevant_symbols)

    hence "evaluate ([(x, True), l1, l2] # [(x, False) # l3 # l4 # c]) (\<rho>(x:=False))"
      using evaluate_def evaluate_clause_def by simp
  }
  moreover
  {
    assume "\<not> evaluate_clause \<rho> [l1, l2]"

    hence "evaluate [l3 # l4 # c] \<rho>" 
      using evaluate_def evaluate_clause_def "1.prems"(2) by simp

    moreover have "x \<triangleright> [l3 # l4 # c]" 
      using "1.prems"(1) by auto
    hence "x \<notin> symbols [l3 # l4 # c]" 
      using all_below_notin_symbols by blast

    ultimately have "evaluate [l3 # l4 # c] (\<rho>(x:=True))"
      by (metis fun_upd_other evaluate_irrelevant_symbols)

    hence "evaluate ([(x, True), l1, l2] # [(x, False) # l3 # l4 # c]) (\<rho>(x:=True))"
      using evaluate_def evaluate_clause_def by auto
  }
  ultimately obtain b where
    "evaluate ([(x, True), l1, l2] # [(x, False) # l3 # l4 # c]) (\<rho>(x:=b))" by blast

  hence e: "evaluate_clause (\<rho>(x:=b)) ([(x, True), l1, l2])" 
    and "evaluate [(x, False) # l3 # l4 # c] (\<rho>(x:=b))" using evaluate_def by auto

  from "1.hyps"[OF w2 this(2)] obtain \<rho>' x' cs where
    "reduce_clause (x + 1) ((x, False) # l3 # l4 # c) = (x', cs)" and
    "evaluate cs \<rho>'" and 
    a: "agree_upto (x + 1) \<rho>' (\<rho>(x:=b))"
    using prod.exhaust_sel by blast

  moreover have "evaluate_clause \<rho>' [(x, True), l1, l2]"
    using switch_valuation[OF a w1] e evaluate_def by auto

  moreover have "agree_upto x \<rho>' \<rho>" using a by auto

  ultimately show ?case
    apply (rule_tac exI[of _ "\<rho>'"])
    apply (cases "reduce_clause (Suc x) ((x, False) # l3 # l4 # c)")
    apply (auto simp add: evaluate_def)
    done

qed (auto)

text \<open> If all symbols in q are below x and \<rho> satisfies q, then there will exist a
       \<rho>' that agrees with \<rho> up to x and that satisfies the reduction of q at x. \<close>
lemma equiv_agree_reduce2:
  assumes "x \<triangleright> q"
  assumes "evaluate q \<rho>"
  shows "\<exists>\<rho>'. evaluate (reduce x q) \<rho>' \<and> agree_upto x \<rho>' \<rho>"
using assms 
proof (induct q arbitrary: \<rho> x)
  case Nil
  thus ?case by auto
next
  case (Cons c q)

  from Cons.prems(1) have "x \<triangleright> [c]" and "x \<triangleright> q" by simp+

  then obtain x' cs where 
    r: "reduce_clause x c = (x', cs)" and "x \<le> x'" and "x' \<triangleright> cs" 
    using reduce_clause_mono reduce_clause_all_below by (metis split_pairs)

  with `x \<triangleright> q` have "x' \<triangleright> q" by fastforce

  from Cons.prems(2) have "evaluate [c] \<rho>" and "evaluate q \<rho>" using evaluate_def by simp+

  from equiv_agree_reduce_clause2[OF `x \<triangleright> [c]` this(1)] obtain \<rho>2 
    where e1: "evaluate cs \<rho>2" and a1: "agree_upto x \<rho>2 \<rho>" using r by auto

  hence "evaluate q \<rho>2" using switch_valuation `evaluate q \<rho>` `x \<triangleright> q` by blast

  from Cons.hyps[OF `x' \<triangleright> q` this] obtain \<rho>3 
    where e2: "evaluate (reduce x' q) \<rho>3" and a2: "agree_upto x' \<rho>3 \<rho>2" by blast

  from this(2) `x \<le> x'` have "agree_upto x \<rho>3 \<rho>2" by simp

  with a1 have a3: "agree_upto x \<rho>3 \<rho>" by simp 

  hence "evaluate cs \<rho>3" using switch_valuation e1 a2 `x' \<triangleright> cs` by blast

  with e2 have "evaluate (cs @ reduce x' q) \<rho>3" using evaluate_def by auto

  hence "evaluate (reduce x (c # q)) \<rho>3" using r by auto

  thus ?case using a3 by blast
qed

text \<open> If q is satisfiable, and all the symbols in q are below x, 
  then reduce x q is also satisfiable. \<close>
theorem sat_reduce2:
  assumes "satisfiable q" and "x \<triangleright> q"
  shows "satisfiable (reduce x q)"
  using assms equiv_agree_reduce2 satisfiable_def by blast

text \<open> If all symbols in q are below x, then q and its reduction at x are equisatisfiable. \<close>
corollary sat_reduce:
  assumes "x \<triangleright> q"
  shows "satisfiable q = satisfiable (reduce x q)"
  using assms sat_reduce1 sat_reduce2 by blast

text \<open> Bonus: Calculating the smallest unused symbol. \<close>
definition fresh_sym :: "query \<Rightarrow> symbol"
where
  "fresh_sym q \<equiv> if symbols q = {} then 0 else Max (symbols q) + 1"

text \<open> The fresh_sym function works on clauses: all symbols in `c` are below `fresh_sym c`. \<close>
lemma all_below_fresh_sym_clause:
  "fresh_sym [c] \<triangleright> [c]"
proof (induct c)
  case Nil
  thus ?case by simp
next
  case (Cons l c)

  have all_below_mono: "\<And>x y q. x \<le> y \<Longrightarrow> x \<triangleright> q \<Longrightarrow> y \<triangleright> q" by fastforce

  have "fresh_sym [l # c] \<triangleright> [[l]]"
    apply (rule_tac x="fresh_sym [[l]]" in all_below_mono)
     apply (auto simp add: fresh_sym_def symbols_def symbols_clause_def)
    done

  moreover have "fresh_sym [l # c] \<triangleright> [c]"
    apply (rule_tac x="fresh_sym [c]" in all_below_mono)
     apply (simp add: fresh_sym_def symbols_def symbols_clause_def)
    apply (rule Cons.hyps)
    done

  ultimately show ?case by simp
qed

text \<open> The fresh_sym function works: all symbols in `q` are below `fresh_sym q`. \<close>
lemma all_below_fresh_sym:
  "fresh_sym q \<triangleright> q"
proof (induct q)
  case Nil
  thus ?case by simp
next
  case (Cons c q)

  have all_below_mono: "\<And>x y q. x \<le> y \<Longrightarrow> x \<triangleright> q \<Longrightarrow> y \<triangleright> q" by fastforce

  have "fresh_sym (c # q) \<triangleright> [c]"
    apply (rule_tac x="fresh_sym [c]" in all_below_mono)
    apply (auto simp add: fresh_sym_def symbols_def symbols_clause_def)[1]
    apply (auto simp add: all_below_fresh_sym_clause)
    using all_below_fresh_sym_clause by fastforce

  moreover
  have "fresh_sym (c # q) \<triangleright> q" 
    apply (rule_tac x="fresh_sym q" in all_below_mono)
     apply (simp add: fresh_sym_def symbols_def)
     apply (intro impI)
     apply (rule Max_mono)
       apply simp
      apply blast
     apply (simp add: symbols_clause_def)
    apply (rule Cons.hyps)
    done
    
  ultimately show ?case by simp  
qed

text \<open> q and its reduction are equisatisfiable. \<close>
theorem sat_reduce_fresh:
  "satisfiable q = satisfiable (reduce (fresh_sym q) q)"
  using sat_reduce all_below_fresh_sym by blast


end