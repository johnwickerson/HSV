theory HSV_tasks_2022_solutions imports Complex_Main begin

section \<open> Task 1: Full adders \<close>

fun halfadder :: "bool * bool \<Rightarrow> bool * bool"
where
  "halfadder (a,b) = (let s = a\<noteq>b in let c = a&b in (c, s))"

fun fulladder :: "bool * bool * bool \<Rightarrow> bool * bool"
where
  "fulladder (a,b,cin) = (
   let (tmp1, tmp2) = halfadder(a,b) in
   let (tmp3, s) = halfadder(cin,tmp2) in
   let cout = tmp1 | tmp3 in
   (cout, s))"

fun nat_from_bool :: "bool \<Rightarrow> nat"
where
  "nat_from_bool False = 0"
| "nat_from_bool True = 1"

theorem fulladder_correct: 
  "fulladder(a,b,cin) = (cout,s) \<Longrightarrow>  
    2 * nat_from_bool cout + nat_from_bool s = 
      nat_from_bool a + nat_from_bool b + nat_from_bool cin"
by auto

fun nat_from_2bool :: "bool * bool \<Rightarrow> nat"
where
  "nat_from_2bool (False, False) = 0"
| "nat_from_2bool (False, True) = 1"
| "nat_from_2bool (True, False) = 2"
| "nat_from_2bool (True, True) = 3"

theorem fulladder_correct_v2: 
  "fulladder(a,b,cin) = (cout,s) \<Longrightarrow>  
  nat_from_2bool (cout,s) = nat_from_bool a + nat_from_bool b + nat_from_bool cin"
by (smt (z3) add_cancel_left_left fulladder.simps halfadder.simps nat_from_2bool.simps 
  nat_from_bool.simps numeral_Bit1 numeral_One one_add_one split_conv verit_sum_simplify)


section \<open> Task 2: Fifth powers \<close>

theorem "(n::nat) ^ 5 mod 10 = n mod 10"
proof (induct n)
  case 0
  thus ?case by simp
next
  case (Suc n)

  have *: "(n + 1)^5 = n^5 + 10*(n^3 + n^2) + 5*n*(n^3 + 1) + 1" 
    by algebra

  have **: "5 * n * (n ^ 3 + 1) mod 10 = 0"
  proof (cases "odd n")
    case True
    hence "odd (n ^ 3)" by simp
    thus ?thesis
      by (metis (no_types, lifting) even_add even_iff_mod_2_eq_zero even_mult_iff 
         mult.assoc mult_0_right mult_2_right mult_mod_right numeral_Bit0 odd_one)
  next
    case False
    thus ?thesis by simp
  qed

  have "Suc n ^ 5 mod 10 = (n + 1)^5 mod 10" 
    by simp
  also have "... = (n^5 + 10*(n^3 + n^2) + 5*n*(n^3 + 1) + 1) mod 10" 
    using * by auto
  also have "... = Suc n mod 10"
    apply (subst mod_add_eq[symmetric])
    apply (subst mod_add_eq[symmetric])
    apply (subst mod_add_eq[symmetric])
    apply (subst Suc)
    apply (subst **)
    using mod_simps(11) apply auto
    done
  finally show ?case by auto
qed

theorem "(n::nat) ^ 6 mod 10 = n mod 10"
  oops (* Counterexample when n=2 *)

section \<open> Task 3: Logic optimisation \<close>

(* Datatype for representing simple circuits. *)
datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

(* Simulates a circuit given a valuation for each input wire. *)
fun simulate where
  "simulate (AND c1 c2) \<rho> = ((simulate c1 \<rho>) \<and> (simulate c2 \<rho>))"
| "simulate (OR c1 c2) \<rho> = ((simulate c1 \<rho>) \<or> (simulate c2 \<rho>))"
| "simulate (NOT c) \<rho> = (\<not> (simulate c \<rho>))"
| "simulate TRUE \<rho> = True"
| "simulate FALSE \<rho> = False"
| "simulate (INPUT i) \<rho> = \<rho> i"

(* Equivalence between circuits. *)
fun circuits_equiv (infix "\<sim>" 50) (* the "50" indicates the operator precedence *) where
  "c1 \<sim> c2 = (\<forall>\<rho>. simulate c1 \<rho> = simulate c2 \<rho>)"

(* An optimisation that exploits the following Boolean identities:
  `a | a = a`
  `a & a = a`
 *)
fun opt_ident where
  "opt_ident (NOT c) = NOT (opt_ident c)"
| "opt_ident (AND c1 c2) = (
   let c1' = opt_ident c1 in
   let c2' = opt_ident c2 in
   if c1' = c2' then c1' else AND c1' c2')"
| "opt_ident (OR c1 c2) = (
   let c1' = opt_ident c1 in
   let c2' = opt_ident c2 in
   if c1' = c2' then c1' else OR c1' c2')"
| "opt_ident TRUE = TRUE"
| "opt_ident FALSE = FALSE"
| "opt_ident (INPUT i) = INPUT i"

lemma (* test case *) 
  "opt_ident (AND (INPUT 1) (OR (INPUT 1) (INPUT 1))) = INPUT 1" 
by eval

theorem opt_ident_is_sound: "opt_ident c \<sim> c"
proof (induct c)
  case (AND c1 c2)
  let ?c1' = "opt_ident c1"
  let ?c2' = "opt_ident c2"
  have "opt_ident (AND c1 c2) 
                 = (if ?c1' = ?c2' then ?c1' else AND ?c1' ?c2')" by auto
  also have "... \<sim> AND c1 c2" using AND by auto
  finally show ?case by blast
next
  case (OR c1 c2)
  let ?c1' = "opt_ident c1"
  let ?c2' = "opt_ident c2"
  have "opt_ident (OR c1 c2) 
                 = (if ?c1' = ?c2' then ?c1' else OR ?c1' ?c2')" by auto
  also have "... \<sim> OR c1 c2" using OR by auto
  finally show ?case by blast
qed(auto)

fun area :: "circuit \<Rightarrow> nat" where
  "area (NOT c) = 1 + area c"
| "area (AND c1 c2) = 1 + area c1 + area c2"
| "area (OR c1 c2) = 1 + area c1 + area c2"
| "area _ = 0"

theorem opt_ident_doesnt_increase_area: 
  "area (opt_ident c) \<le> area c"
proof (induct c)
  case (AND c1 c2)
  thus ?case by (cases "opt_ident c1 = opt_ident c2", auto)
next
  case (OR c1 c2)
  thus ?case by (cases "opt_ident c1 = opt_ident c2", auto)
qed(simp+)



section \<open> Task 4: More logic optimisation \<close>

(* An optimisation that exploits the following Boolean identities:
  `a | (a & b) = a`
  `(a & b) | a = a`
  `a & (a | b) = a`
  `(a | b) & a = a`
 *)
fun opt_redundancy where
  "opt_redundancy (OR c1 (AND c2 c3)) = (
   let c1' = opt_redundancy c1 in
   let c2' = opt_redundancy c2 in
   let c3' = opt_redundancy c3 in
   if c1' = c2' \<or> c1' = c3' then c1' else
   OR c1' (AND c2' c3'))"
| "opt_redundancy (OR (AND c2 c3) c1) = (
   let c1' = opt_redundancy c1 in
   let c2' = opt_redundancy c2 in
   let c3' = opt_redundancy c3 in
   if c1' = c2' \<or> c1' = c3' then c1' else
   OR (AND c2' c3') c1')"
| "opt_redundancy (AND c1 (OR c2 c3)) = (
   let c1' = opt_redundancy c1 in
   let c2' = opt_redundancy c2 in
   let c3' = opt_redundancy c3 in
   if c1' = c2' \<or> c1' = c3' then c1' else
   AND c1' (OR c2' c3'))"
| "opt_redundancy (AND (OR c2 c3) c1) = (
   let c1' = opt_redundancy c1 in
   let c2' = opt_redundancy c2 in
   let c3' = opt_redundancy c3 in
   if c1' = c2' \<or> c1' = c3' then c1' else
   AND (OR c2' c3') c1')"
| "opt_redundancy (NOT c) = NOT (opt_redundancy c)"
| "opt_redundancy (AND c1 c2) = AND (opt_redundancy c1) (opt_redundancy c2)"
| "opt_redundancy (OR c1 c2) = OR (opt_redundancy c1) (opt_redundancy c2)"
| "opt_redundancy TRUE = TRUE"
| "opt_redundancy FALSE = FALSE"
| "opt_redundancy (INPUT i) = INPUT i"

(* Rename the `opt_redundancy.induct` theorem to `opt_redundancy_induct` and
   while doing so, rename the first several cases to more useful names. *)
lemmas opt_redundancy_induct = opt_redundancy.induct[case_names
  OR__AND OR_AND_NOT OR_AND_OR OR_AND_TRUE OR_AND_FALSE OR_AND_INPUT
  AND__OR AND_OR_NOT AND_OR_OR AND_OR_TRUE AND_OR_FALSE AND_OR_INPUT NOT]

lemma (* test case *) 
  "opt_redundancy (AND (INPUT 1) (OR (INPUT 1) (INPUT 2))) 
   = INPUT 1" 
by eval
lemma (* test case *) 
  "opt_redundancy (AND (AND (INPUT 1) (OR (INPUT 1) (INPUT 2)))
                       (OR (AND (INPUT 1) (OR (INPUT 1) (INPUT 2))) (INPUT 2))) 
   = INPUT 1" 
by eval
lemma (* test case *) 
  "opt_redundancy (AND (AND (INPUT 1) (OR (INPUT 1) (INPUT 2))) 
                       (OR (INPUT 2) (AND (INPUT 1) (OR (INPUT 1) (INPUT 2))))) 
   = INPUT 1"
by eval
lemma (* test case *) 
  "opt_redundancy (AND (AND (AND (INPUT 1) (OR (INPUT 1) (INPUT 2))) 
                            (OR (INPUT 2) (AND (INPUT 1) (OR (INPUT 1) (INPUT 2))))) 
                       (OR (INPUT 1) (INPUT 2))) 
  = INPUT 1" 
by eval

theorem opt_redundancy_is_sound: "opt_redundancy c \<sim> c"
proof (induct rule: opt_redundancy_induct)
  case (OR__AND c1 c2 c3)
  let ?c1' = "opt_redundancy c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  from OR__AND have IH: "?c1' \<sim> c1" "?c2' \<sim> c2" "?c3' \<sim> c3" by auto
  have "opt_redundancy (OR c1 (AND c2 c3)) = (
        if ?c1' = ?c2' \<or> ?c1' = ?c3' then ?c1' else
        OR ?c1' (AND ?c2' ?c3'))" by auto
  also have "... \<sim> OR c1 (AND c2 c3)" using IH by auto
  finally show ?case by blast
next
  case (OR_AND_NOT c2 c3 c4)
  let ?c1 = "NOT c4"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  from OR_AND_NOT have IH: "?c1' \<sim> ?c1" "?c2' \<sim> c2" "?c3' \<sim> c3" by auto
  have "opt_redundancy (OR (AND c2 c3) ?c1) = (
        if ?c1' = ?c2' \<or> ?c1' = ?c3' then ?c1' else
        OR (AND ?c2' ?c3') ?c1')" by auto
  also have "... \<sim> OR (AND c2 c3) ?c1" using IH
    by (smt (z3) circuits_equiv.elims simulate.simps)
  finally show ?case by blast
next
  case (OR_AND_OR c2 c3 c4 c5)
  let ?c1 = "OR c4 c5"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  from OR_AND_OR have IH: "?c1' \<sim> ?c1" "?c2' \<sim> c2" "?c3' \<sim> c3" by auto
  have "opt_redundancy (OR (AND c2 c3) ?c1) = (
        if ?c1' = ?c2' \<or> ?c1' = ?c3' then ?c1' else
        OR (AND ?c2' ?c3') ?c1')" by auto
  also have "... \<sim> OR (AND c2 c3) ?c1" using IH
    by (smt (z3) circuits_equiv.elims simulate.simps)
  finally show ?case by blast
next
  case (OR_AND_TRUE c2 c3)
  let ?c1 = "TRUE"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  from OR_AND_TRUE have IH: "?c1' \<sim> ?c1" "?c2' \<sim> c2" "?c3' \<sim> c3" by auto
  have "opt_redundancy (OR (AND c2 c3) ?c1) = (
        if ?c1' = ?c2' \<or> ?c1' = ?c3' then ?c1' else
        OR (AND ?c2' ?c3') ?c1')" by auto
  also have "... \<sim> OR (AND c2 c3) ?c1" using IH
    by (smt (z3) circuits_equiv.elims simulate.simps)
  finally show ?case by blast
next
  case (OR_AND_FALSE c2 c3)
  let ?c1 = "FALSE"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  from OR_AND_FALSE have IH: "?c1' \<sim> ?c1" "?c2' \<sim> c2" "?c3' \<sim> c3" by auto
  have "opt_redundancy (OR (AND c2 c3) ?c1) = (
        if ?c1' = ?c2' \<or> ?c1' = ?c3' then ?c1' else
        OR (AND ?c2' ?c3') ?c1')" by auto
  also have "... \<sim> OR (AND c2 c3) ?c1" using IH
    by (smt (z3) circuits_equiv.elims simulate.simps)
  finally show ?case by blast
next
  case (OR_AND_INPUT c2 c3 i)
  let ?c1 = "INPUT i"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  from OR_AND_INPUT have IH: "?c1' \<sim> ?c1" "?c2' \<sim> c2" "?c3' \<sim> c3" by auto
  have "opt_redundancy (OR (AND c2 c3) ?c1) = (
        if ?c1' = ?c2' \<or> ?c1' = ?c3' then ?c1' else
        OR (AND ?c2' ?c3') ?c1')" by auto
  also have "... \<sim> OR (AND c2 c3) ?c1" using IH 
    by (smt (z3) circuits_equiv.elims simulate.simps)
  finally show ?case by blast
next
  case (AND__OR c1 c2 c3)
  let ?c1' = "opt_redundancy c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  from AND__OR have IH: "?c1' \<sim> c1" "?c2' \<sim> c2" "?c3' \<sim> c3" by auto
  have "opt_redundancy (AND c1 (OR c2 c3)) = (
        if ?c1' = ?c2' \<or> ?c1' = ?c3' then ?c1' else
        AND ?c1' (OR ?c2' ?c3'))" by auto
  also have "... \<sim> AND c1 (OR c2 c3)" using IH by auto
  finally show ?case by blast
next
  case (AND_OR_NOT c2 c3 c4)
  let ?c1 = "NOT c4"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  from AND_OR_NOT have IH: "?c1' \<sim> ?c1" "?c2' \<sim> c2" "?c3' \<sim> c3" by auto
  have "opt_redundancy (AND (OR c2 c3) ?c1) = (
        if ?c1' = ?c2' \<or> ?c1' = ?c3' then ?c1' else
        AND (OR ?c2' ?c3') ?c1')" by auto
  also have "... \<sim> AND (OR c2 c3) ?c1" using IH
    by (smt (z3) circuits_equiv.elims simulate.simps)
  finally show ?case by blast
next
  case (AND_OR_OR c2 c3 c4 c5)
  let ?c1 = "AND c4 c5"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  from AND_OR_OR have IH: "?c1' \<sim> ?c1" "?c2' \<sim> c2" "?c3' \<sim> c3" by auto
  have "opt_redundancy (AND (OR c2 c3) ?c1) = (
        if ?c1' = ?c2' \<or> ?c1' = ?c3' then ?c1' else
        AND (OR ?c2' ?c3') ?c1')" by auto
  also have "... \<sim> AND (OR c2 c3) ?c1" using IH
    by (smt (z3) circuits_equiv.elims simulate.simps)
  finally show ?case by blast
next
  case (AND_OR_TRUE c2 c3)
  let ?c1 = "TRUE"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  from AND_OR_TRUE have IH: "?c1' \<sim> ?c1" "?c2' \<sim> c2" "?c3' \<sim> c3" by auto
  have "opt_redundancy (AND (OR c2 c3) ?c1) = (
        if ?c1' = ?c2' \<or> ?c1' = ?c3' then ?c1' else
        AND (OR ?c2' ?c3') ?c1')" by auto
  also have "... \<sim> AND (OR c2 c3) ?c1" using IH
    by (smt (z3) circuits_equiv.elims simulate.simps)
  finally show ?case by blast
next
  case (AND_OR_FALSE c2 c3)
  let ?c1 = "FALSE"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  from AND_OR_FALSE have IH: "?c1' \<sim> ?c1" "?c2' \<sim> c2" "?c3' \<sim> c3" by auto
  have "opt_redundancy (AND (OR c2 c3) ?c1) = (
        if ?c1' = ?c2' \<or> ?c1' = ?c3' then ?c1' else
        AND (OR ?c2' ?c3') ?c1')" by auto
  also have "... \<sim> AND (OR c2 c3) ?c1" using IH
    by (smt (z3) circuits_equiv.elims simulate.simps)
  finally show ?case by blast
next
  case (AND_OR_INPUT c2 c3 i)
  let ?c1 = "INPUT i"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  from AND_OR_INPUT have IH: "?c1' \<sim> ?c1" "?c2' \<sim> c2" "?c3' \<sim> c3" by auto
  have "opt_redundancy (AND (OR c2 c3) ?c1) = (
        if ?c1' = ?c2' \<or> ?c1' = ?c3' then ?c1' else
        AND (OR ?c2' ?c3') ?c1')" by auto
  also have "... \<sim> AND (OR c2 c3) ?c1" using IH
    by (smt (z3) circuits_equiv.elims simulate.simps)
  finally show ?case by blast
qed(auto)
  

theorem opt_redundancy_doesnt_increase_area: 
  "area (opt_redundancy c) \<le> area c"
proof (induct rule: opt_redundancy_induct)
  case (OR__AND c1 c2 c3)
  let ?c1' = "opt_redundancy c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  have "area ?c1' \<le> area c1" "area ?c2' \<le> area c2" "area ?c3' \<le> area c3" 
    using OR__AND by auto
  thus ?case by (cases "?c1' = ?c2' \<or> ?c1' = ?c3'", auto)
next
  case (OR_AND_NOT c2 c3 v)
  let ?c1 = "NOT v"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  have "area ?c1' \<le> area ?c1" "area ?c2' \<le> area c2" "area ?c3' \<le> area c3" 
    using OR_AND_NOT by auto
  thus ?case by (cases "?c1' = ?c2' \<or> ?c1' = ?c3'", auto)
next
  case (OR_AND_OR c2 c3 v va)
  let ?c1 = "OR v va"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  have "area ?c1' \<le> area ?c1" "area ?c2' \<le> area c2" "area ?c3' \<le> area c3" 
    using OR_AND_OR by auto
  thus ?case by (cases "?c1' = ?c2' \<or> ?c1' = ?c3'", auto)
next
  case (OR_AND_TRUE c2 c3)
  let ?c1 = "TRUE"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  have "area ?c1' \<le> area ?c1" "area ?c2' \<le> area c2" "area ?c3' \<le> area c3" 
    using OR_AND_TRUE by auto
  thus ?case by (cases "?c1' = ?c2' \<or> ?c1' = ?c3'", auto)
next
  case (OR_AND_FALSE c2 c3)
  let ?c1 = "FALSE"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  have "area ?c1' \<le> area ?c1" "area ?c2' \<le> area c2" "area ?c3' \<le> area c3" 
    using OR_AND_FALSE by auto
  thus ?case by (cases "?c1' = ?c2' \<or> ?c1' = ?c3'", auto)
next
  case (OR_AND_INPUT c2 c3 v)
  let ?c1 = "INPUT v"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  have "area ?c1' \<le> area ?c1" "area ?c2' \<le> area c2" "area ?c3' \<le> area c3" 
    using OR_AND_INPUT by auto
  thus ?case by (cases "?c1' = ?c2' \<or> ?c1' = ?c3'", auto)
next
  case (AND__OR c1 c2 c3)
  let ?c1' = "opt_redundancy c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  have "area ?c1' \<le> area c1" "area ?c2' \<le> area c2" "area ?c3' \<le> area c3" 
    using AND__OR by auto
  thus ?case by (cases "?c1' = ?c2' \<or> ?c1' = ?c3'", auto)
next
  case (AND_OR_NOT c2 c3 v)
  let ?c1 = "NOT v"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  have "area ?c1' \<le> area ?c1" "area ?c2' \<le> area c2" "area ?c3' \<le> area c3" 
    using AND_OR_NOT by auto
  thus ?case by (cases "?c1' = ?c2' \<or> ?c1' = ?c3'", auto)
next
  case (AND_OR_OR c2 c3 v va)
  let ?c1 = "AND v va"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  have "area ?c1' \<le> area ?c1" "area ?c2' \<le> area c2" "area ?c3' \<le> area c3" 
    using AND_OR_OR by auto
  thus ?case by (cases "?c1' = ?c2' \<or> ?c1' = ?c3'", auto)
next
  case (AND_OR_TRUE c2 c3)
  let ?c1 = "TRUE"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  have "area ?c1' \<le> area ?c1" "area ?c2' \<le> area c2" "area ?c3' \<le> area c3" 
    using AND_OR_TRUE by auto
  thus ?case by (cases "?c1' = ?c2' \<or> ?c1' = ?c3'", auto)
next
  case (AND_OR_FALSE c2 c3)
  let ?c1 = "FALSE"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  have "area ?c1' \<le> area ?c1" "area ?c2' \<le> area c2" "area ?c3' \<le> area c3" 
    using AND_OR_FALSE by auto
  thus ?case by (cases "?c1' = ?c2' \<or> ?c1' = ?c3'", auto)
next
  case (AND_OR_INPUT c2 c3 v)
  let ?c1 = "INPUT v"
  let ?c1' = "opt_redundancy ?c1"
  let ?c2' = "opt_redundancy c2"
  let ?c3' = "opt_redundancy c3"
  have "area ?c1' \<le> area ?c1" "area ?c2' \<le> area c2" "area ?c3' \<le> area c3" 
    using AND_OR_INPUT by auto
  thus ?case by (cases "?c1' = ?c2' \<or> ?c1' = ?c3'", auto)
qed(auto)


end