theory HSV_tasks_2019_solutions imports Complex_Main begin

section \<open>Task 1: proving that 2 * sqrt 2 is irrational.\<close>

(* The following theorem is copied from Chapter 3 of the worksheet *)
theorem sqrt2_irrational: "sqrt 2 \<notin> \<rat>"
proof auto
  assume "sqrt 2 \<in> \<rat>"
  then obtain m n where 
    "n \<noteq> 0" and "\<bar>sqrt 2\<bar> = real m / real n" and "coprime m n" 
    by (rule Rats_abs_nat_div_natE)
  hence "\<bar>sqrt 2\<bar>^2 = (real m / real n)^2" by auto 
  hence "2 = (real m / real n)^2" by simp
  hence "2 = (real m)^2 / (real n)^2" unfolding power_divide by auto
  hence "2 * (real n)^2 = (real m)^2"
    by (simp add: nonzero_eq_divide_eq `n \<noteq> 0`)
  hence "real (2 * n^2) = (real m)^2" by auto
  hence *: "2 * n^2 = m^2"
    using of_nat_power_eq_of_nat_cancel_iff by blast
  hence "even (m^2)" by presburger
  hence "even m" by simp
  then obtain m' where "m = 2 * m'" by auto
  with * have "2 * n^2 = (2 * m')^2" by auto
  hence "2 * n^2 = 4 * m'^2" by simp
  hence "n^2 = 2 * m'^2" by simp
  hence "even (n^2)" by presburger
  hence "even n" by simp
  with `even m` and `coprime m n` show False by auto
qed

theorem "2 * sqrt 2 \<notin> \<rat>"
proof auto
  assume *: "2 * sqrt 2 \<in> \<rat>"
  have "2 \<in> \<rat>" by simp
  with * have "2 * sqrt 2 / 2 \<in> \<rat>" using Rats_divide by blast
  hence "sqrt 2 \<in> \<rat>" by simp
  with sqrt2_irrational show False by simp
qed

section \<open>Task 2: L-numbers.\<close>

fun L :: "nat \<Rightarrow> nat" where
  "L n = (if n < 2 then n else 2 + L (n - 1))"

value "L 0" (* should be 0 *)
value "L 1" (* should be 1 *)
value "L 2" (* should be 3 *)
value "L 3" (* should be 5 *)

lemma L_helper: "L (Suc n) = 2 * (Suc n) - 1"
  apply (induct n)
   apply simp+
  done

theorem "L n = (if n = 0 then 0 else 2 * n - 1)"
  apply (cases n)
   apply simp
  using L_helper apply auto
  done

section \<open>Task 3: Pyramidal numbers.\<close>

fun py :: "nat \<Rightarrow> nat" where
  "py n = (if n = 0 then 0 else n^2 + py (n-1))"

value "py 0" (* 0 *)
value "py 1" (* 1 *)
value "py 2" (* 5 *)
value "py 3" (* 14 *)
value "py 4" (* 30 *)
value "py 5" (* 55 *)
value "py 6" (* 91 *)


theorem "py n = ((2 * n + 1) * (n + 1) * n) div 6"
proof (induct n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  assume IH: "py n = ((2 * n + 1) * (n + 1) * n) div 6" (* induction hypothesis *)

  have "py (Suc n) = (Suc n)^2 + py n" by simp
  also have "... = (Suc n)^2 + ((2 * n + 1) * (n + 1) * n) div 6" using IH by simp
  also have "... = (6 * (n + 1)^2 + (2 * n + 1) * (n + 1) * n) div 6" by simp
  also have "... = (6 * (n^2 + 2*n + 1) + (2 * n + 1) * (n + 1) * n) div 6"
    by (metis Suc_eq_plus1 add_Suc mult_2 one_add_one plus_1_eq_Suc power2_sum power_one)
  also have "... = (2 * n * n + 4 * n + 3 * n + 6) * (n + 1) div 6"
    by (simp add: add_mult_distrib power2_eq_square distrib_right)
  also have "... = (2 * n * (n + 2) + 3 * (n + 2)) * (n + 1) div 6"
    by (smt add.assoc distrib_right mult.commute mult_2_right numeral_Bit0)
  also have "... = (2 * n + 3) * (n + 2) * (n + 1) div 6"
    by (simp add: distrib_right)
  also have "... = (2 * Suc n + 1) * (Suc n + 1) * Suc n div 6"
    by (metis One_nat_def Suc_1 Suc_eq_plus1 add_Suc_shift distrib_left mult_2 numeral_3_eq_3)
  finally show "py (Suc n) = (2 * Suc n + 1) * (Suc n + 1) * Suc n div 6" by assumption
qed

section \<open>Task 4: the opt_NOT optimisation leaves no consecutive NOTs in the circuit.\<close>

datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

text \<open>Simulates a circuit given a valuation for each input wire\<close>

fun simulate where
  "simulate (AND c1 c2) \<rho> = ((simulate c1 \<rho>) \<and> (simulate c2 \<rho>))"
| "simulate (OR c1 c2) \<rho> = ((simulate c1 \<rho>) \<or> (simulate c2 \<rho>))"
| "simulate (NOT c) \<rho> = (\<not> (simulate c \<rho>))"
| "simulate TRUE \<rho> = True"
| "simulate FALSE \<rho> = False"
| "simulate (INPUT i) \<rho> = \<rho> i"

text \<open>A function that optimises a circuit by removing pairs of consecutive NOT gates\<close>

fun opt_NOT where
  "opt_NOT (NOT (NOT c)) = opt_NOT c"
| "opt_NOT (NOT c) = NOT (opt_NOT c)"
| "opt_NOT (AND c1 c2) = AND (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT (OR c1 c2) = OR (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT TRUE = TRUE"
| "opt_NOT FALSE = FALSE"
| "opt_NOT (INPUT i) = INPUT i"

text \<open>We can prove that the optimiser does its job: that the optimised 
circuit has no consecutive NOT gates.\<close>

fun has_double_NOT where
  "has_double_NOT (NOT (NOT c)) = True"
| "has_double_NOT (NOT c) = has_double_NOT c"
| "has_double_NOT (AND c1 c2) = (has_double_NOT c1 \<or> has_double_NOT c2)"
| "has_double_NOT (OR c1 c2) = (has_double_NOT c1 \<or> has_double_NOT c2)"
| "has_double_NOT _ = False"

theorem opt_NOT_is_complete: "\<not> has_double_NOT (opt_NOT c)"
  by (induct c rule: opt_NOT.induct, auto)

section \<open>Task 5: Removing NOT-NOT is idempotent.\<close>

text \<open>We can prove that the optimiser is 'idempotent': applying it twice is the 
same as applying it just once.\<close>

theorem opt_NOT_is_idempotent: "opt_NOT (opt_NOT c) = opt_NOT c"
  by (induct c rule: opt_NOT.induct, auto)

section \<open>Task 6: Applying De Morgan's laws is sound.\<close>

text \<open>Optimising based on De Morgan's laws\<close>

fun opt_DM where
  "opt_DM (NOT c) = NOT (opt_DM c)"
| "opt_DM (AND (NOT c1) (NOT c2)) = NOT (OR (opt_DM c1) (opt_DM c2))"
| "opt_DM (AND c1 c2) = AND (opt_DM c1) (opt_DM c2)"
| "opt_DM (OR (NOT c1) (NOT c2)) = NOT (AND (opt_DM c1) (opt_DM c2))"
| "opt_DM (OR c1 c2) = OR (opt_DM c1) (opt_DM c2)"
| "opt_DM TRUE = TRUE"
| "opt_DM FALSE = FALSE"
| "opt_DM (INPUT i) = INPUT i"

theorem opt_DM_is_sound: "simulate (opt_DM c) \<rho> = simulate c \<rho>"
  by (induct rule: opt_DM.induct, auto)

text \<open>The following non-theorem is easily contradicted, e.g. 
  using c = AND (NOT (NOT TRUE)) (NOT (NOT TRUE)). Therefore, 
  opt_DM isn't idempotent.\<close>

theorem opt_DM_is_idempotent: "opt_DM (opt_DM c) = opt_DM c"
  oops

section \<open>Task 7: Applying both optimisations successively is sound.\<close>

(* The following theorem was provided in the worksheet *)
theorem opt_NOT_is_sound: "simulate (opt_NOT c) \<rho> = simulate c \<rho>"
  by (induct rule: opt_NOT.induct, auto)

theorem both_sound: "simulate (opt_DM (opt_NOT c)) \<rho> = simulate c \<rho>"
  apply (subst opt_DM_is_sound)
  apply (subst opt_NOT_is_sound)
  apply auto
  done

section \<open>Task 8: Neither optimisation increases the circuit's area.\<close>

text \<open>The following function calculates the area of a circuit (i.e. number of gates).\<close>

fun area :: "circuit \<Rightarrow> nat" where
  "area (NOT c) = 1 + area c"
| "area (AND c1 c2) = 1 + area c1 + area c2"
| "area (OR c1 c2) = 1 + area c1 + area c2"
| "area _ = 0"

theorem opt_NOT_doesnt_increase_area: "area (opt_NOT c) \<le> area c"
  by (induct rule: opt_NOT.induct, auto)

theorem opt_DM_doesnt_increase_area: "area (opt_DM c) \<le> area c"
  by (induct rule: opt_DM.induct, auto)

section \<open>Task 9: Neither optimisation increases the circuit's delay.\<close>

text \<open>Delay (assuming all gates have a delay of 1, and constants and inputs are instantaneous)\<close>

fun delay :: "circuit \<Rightarrow> nat" where
  "delay (NOT c) = 1 + delay c"
| "delay (AND c1 c2) = 1 + max (delay c1) (delay c2)"
| "delay (OR c1 c2) = 1 + max (delay c1) (delay c2)"
| "delay _ = 0"

text \<open>We can prove that our optimisations never increase the maximum delay of a circuit.\<close>

theorem opt_NOT_doesnt_increase_delay: "delay (opt_NOT c) \<le> delay c"
  by (induct rule: opt_NOT.induct, auto)

theorem opt_DM_doesnt_increase_delay: "delay (opt_DM c) \<le> delay c"
  by (induct rule: opt_DM.induct, auto)

section \<open>Task 10: Constant folding.\<close>

text \<open>Here is an optimiser that performs 'constant folding': wherever it sees a gate with
constants (TRUE and FALSE) as inputs, it tries to replace the gate with TRUE, FALSE, or the other
input depending on the logical behaviour of the gate.

For instance, it replaces NOT FALSE with TRUE, AND FALSE c with FALSE for all inputs c, and
OR c FALSE with c.

This optimiser is somewhat more complicated than the other optimisers: it has a lot of rules, and
needs to do analysis on the results of recursively applying itself.

First, we define how it translates NOT gates, AND gates, and OR gates:\<close>

fun opt_CF_NOT where
  "opt_CF_NOT TRUE  = FALSE"
| "opt_CF_NOT FALSE = TRUE"
| "opt_CF_NOT c     = NOT c"

fun opt_CF_AND where
  "opt_CF_AND TRUE  c2     = c2"
| "opt_CF_AND c1     TRUE  = c1"
| "opt_CF_AND FALSE _     = FALSE"
| "opt_CF_AND _     FALSE = FALSE"
| "opt_CF_AND c1     c2     = AND c1 c2"

fun opt_CF_OR where
  "opt_CF_OR FALSE c2     = c2"
| "opt_CF_OR c1     FALSE = c1"
| "opt_CF_OR TRUE  _     = TRUE"
| "opt_CF_OR _     TRUE  = TRUE"
| "opt_CF_OR c1     c2     = OR c1 c2"

text \<open>The actual optimiser just runs the above rewrites on each NOT, AND, and OR gate.\<close>

fun opt_CF where
  "opt_CF (NOT c) = opt_CF_NOT (opt_CF c)"
| "opt_CF (AND c1 c2) = opt_CF_AND (opt_CF c1) (opt_CF c2)"
| "opt_CF (OR c1 c2) = opt_CF_OR  (opt_CF c1) (opt_CF c2)"
| "opt_CF x = x"

text \<open>To prove the constant folder sound, first consider the soundness of the sub-cases.\<close>

lemma opt_CF_NOT_is_sound: "simulate (opt_CF_NOT c) \<rho> = simulate (NOT c) \<rho>"
  by (cases c, auto)

lemma opt_CF_AND_is_sound: "simulate (opt_CF_AND c1 c2) \<rho> = simulate (AND c1 c2) \<rho>"
  by (induct c1 c2 rule: opt_CF_AND.induct, auto)

lemma opt_CF_OR_is_sound: "simulate (opt_CF_OR c1 c2) \<rho> = simulate (OR c1 c2) \<rho>"
  by (induct c1 c2 rule: opt_CF_OR.induct, auto)

theorem opt_CF_is_sound: "simulate (opt_CF c) \<rho> = simulate c \<rho>"
  by (induct c rule: opt_CF.induct,
      auto simp add: opt_CF_NOT_is_sound opt_CF_AND_is_sound opt_CF_OR_is_sound)

text \<open>To get an idea of whether the constant folder is complete, we can see whether it reduces a
circuit with only constant inputs into a single TRUE or FALSE constant.  First, define what it
means for a circuit to have no inputs, and to be only a constant.\<close>

fun no_inputs where
  "no_inputs (NOT c) = no_inputs c"
| "no_inputs (AND c1 c2) = (no_inputs c1 \<and> no_inputs c2)"
| "no_inputs (OR c1 c2) = (no_inputs c1 \<and> no_inputs c2)"
| "no_inputs (INPUT _) = False"
| "no_inputs _ = True"

fun is_constant where
  "is_constant c = (c = TRUE \<or> c = FALSE)"

lemma opt_CF_NOT_reduce:
  assumes "is_constant c"
  shows "is_constant (opt_CF_NOT c)"
  using assms
  by (cases c, auto)

lemma opt_CF_AND_reduce:
  assumes "is_constant c1" and "is_constant c2"
  shows "is_constant (opt_CF_AND c1 c2)"
  using assms
  by (induct c1 c2 rule: opt_CF_AND.induct, auto)

lemma opt_CF_OR_reduce:
  assumes "is_constant c1" and "is_constant c2"
  shows "is_constant (opt_CF_OR c1 c2)"
  using assms
  by (induct c1 c2 rule: opt_CF_OR.induct, auto)

theorem opt_CF_reduce:
  assumes "no_inputs c"
  shows "is_constant (opt_CF c)"
  using assms
  by (induct c rule: opt_CF.induct,
      auto simp add: opt_CF_NOT_reduce opt_CF_AND_reduce opt_CF_OR_reduce)

lemma opt_CF_NOT_doesnt_increase_area: "area (opt_CF_NOT c) \<le> area (NOT c)"
  by (cases c, auto)

lemma opt_CF_AND_doesnt_increase_area: "area (opt_CF_AND c1 c2) \<le> area (AND c1 c2)"
  by (induct c1 c2 rule: opt_CF_AND.induct, auto)

lemma opt_CF_OR_doesnt_increase_area: "area (opt_CF_OR c1 c2) \<le> area (OR c1 c2)"
  by (induct c1 c2 rule: opt_CF_OR.induct, auto)

theorem opt_CF_doesnt_increase_area: "area (opt_CF c) \<le> area c"
proof (induct rule: opt_CF.induct)
  case (1 c) 
  have "area (opt_CF (NOT c)) 
                 = area (opt_CF_NOT (opt_CF c))" by simp
  also have "... \<le> area (NOT (opt_CF c))" 
    using opt_CF_NOT_doesnt_increase_area by assumption
  also have "... \<le> area (NOT c)" using 1 by simp
  finally show ?case by assumption
next
  case (2 c1 c2)
  have "area (opt_CF (AND c1 c2)) 
                 = area (opt_CF_AND (opt_CF c1) (opt_CF c2))" by simp
  also have "... \<le> area (AND (opt_CF c1) (opt_CF c2))" 
    using opt_CF_AND_doesnt_increase_area by assumption
  also have "... \<le> area (AND c1 c2)" using 2 by simp
  finally show ?case by assumption
next
  case (3 c1 c2)
  have "area (opt_CF (OR c1 c2)) 
                 = area (opt_CF_OR (opt_CF c1) (opt_CF c2))" by simp
  also have "... \<le> area (OR (opt_CF c1) (opt_CF c2))" 
    using opt_CF_OR_doesnt_increase_area by assumption
  also have "... \<le> area (OR c1 c2)" using 3 by simp
  finally show ?case by assumption
qed simp+

lemma opt_CF_NOT_doesnt_increase_delay: "delay (opt_CF_NOT c) \<le> delay (NOT c)"
  by (cases c, auto)

lemma opt_CF_AND_doesnt_increase_delay: "delay (opt_CF_AND c1 c2) \<le> delay (AND c1 c2)"
  by (induct c1 c2 rule: opt_CF_AND.induct, auto)

lemma opt_CF_OR_doesnt_increase_delay: "delay (opt_CF_OR c1 c2) \<le> delay (OR c1 c2)"
  by (induct c1 c2 rule: opt_CF_OR.induct, auto)

theorem opt_CF_doesnt_increase_delay: "delay (opt_CF c) \<le> delay c"
proof (induct rule: opt_CF.induct)
  case (1 c) 
  have "delay (opt_CF (NOT c)) 
                 = delay (opt_CF_NOT (opt_CF c))" by simp
  also have "... \<le> delay (NOT (opt_CF c))" 
    using opt_CF_NOT_doesnt_increase_delay by assumption
  also have "... \<le> delay (NOT c)" using 1 by simp
  finally show ?case by assumption
next
  case (2 c1 c2)
  have "delay (opt_CF (AND c1 c2)) 
                 = delay (opt_CF_AND (opt_CF c1) (opt_CF c2))" by simp
  also have "... \<le> delay (AND (opt_CF c1) (opt_CF c2))" 
    using opt_CF_AND_doesnt_increase_delay by assumption
  also have "... \<le> delay (AND c1 c2)" using 2 by auto
  finally show ?case by assumption
next
  case (3 c1 c2)
  have "delay (opt_CF (OR c1 c2)) 
                 = delay (opt_CF_OR (opt_CF c1) (opt_CF c2))" by simp
  also have "... \<le> delay (OR (opt_CF c1) (opt_CF c2))" 
    using opt_CF_OR_doesnt_increase_delay by assumption
  also have "... \<le> delay (OR c1 c2)" using 3 by auto
  finally show ?case by assumption
qed simp+

section \<open>Task 11: Adding fan-out.\<close>

text \<open>Please see separate file.\<close>

end