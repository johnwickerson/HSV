theory HSV_tasks_2020_solutions imports Complex_Main begin

section \<open>Task 1: proving that "3 / sqrt 2" is irrational.\<close>

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

theorem "3 / sqrt 2 \<notin> \<rat>"
proof auto
  assume *: "3 / sqrt 2 \<in> \<rat>"

  (* establish that 3 / sqrt 2 = 3 * sqrt 2 / 2 *)
  have "3 / sqrt 2 = (3 / sqrt 2) * (sqrt 2 / sqrt 2)" by auto
  also have "... = 3 * sqrt 2 / (sqrt 2 * sqrt 2)" by argo
  also have "... = 3 * sqrt 2 / 2" by simp
  finally have "3 / sqrt 2 = 3 * sqrt 2 / 2" by assumption

  (* so 3 * sqrt 2 / 2 is rational ... *)
  with * have "3 * sqrt 2 / 2 \<in> \<rat>" by auto

  (* ... and 2/3 is also rational ... *)
  moreover have "2 / 3 \<in> \<rat>" by simp

  (* ... so their product is also rational ... *)
  ultimately have "(3 * sqrt 2 / 2) * (2 / 3) \<in> \<rat>" 
    using Rats_mult by blast

  (* ... which means sqrt 2 is rational ... *)
  hence "sqrt 2 \<in> \<rat>" by simp

  (* ... which contradicts the previous theorem! *)
  with sqrt2_irrational show False by simp
qed

section \<open>Task 2: Centred pentagonal numbers.\<close>

fun pent :: "nat \<Rightarrow> nat" where
  "pent n = (if n = 0 then 1 else 5 * n + pent (n - 1))"

value "pent 0" (* should be 1 *)
value "pent 1" (* should be 6 *)
value "pent 2" (* should be 16 *)
value "pent 3" (* should be 31 *)

theorem "pent n = (5 * n^2 + 5 * n + 2) div 2"
proof (induct n)
  case 0
  thus ?case by auto
next
  case (Suc n)
  have "pent (Suc n) = 5 * (n + 1) + pent n" by simp
  also have "... = 5 * n + 5 + (5 * n^2 + 5 * n + 2) div 2" using Suc by simp
  also have "... = (5 * (n^2 + 2 * n + 1) + 5 * (n + 1) + 2) div 2" by simp
  also have "... = (5 * (n + 1)^2 + 5 * (n + 1) + 2) div 2"
    by (smt add.commute add_Suc mult_2 one_add_one plus_1_eq_Suc power2_sum power_one)
  also have "... = (5 * (Suc n)^2 + 5 * Suc n + 2) div 2" by simp
  finally show ?case by assumption
qed
  

section \<open>Task 3: Lucas numbers.\<close>

fun luc :: "nat \<Rightarrow> nat" where
  "luc n = (if n = 0 then 2 else if n = 1 then 1 else luc (n - 1) + luc (n - 2))"

value "luc 0" (* should be 2 *)
value "luc 1" (* should be 1 *)
value "luc 2" (* should be 3 *)
value "luc 3" (* should be 4 *)

fun fib :: "nat \<Rightarrow> nat" where
  "fib n = (if n = 0 then 0 else if n = 1 then 1 else fib (n - 1) + fib (n - 2))"

value "fib 0" (* should be 0 *)
value "fib 1" (* should be 1 *)
value "fib 2" (* should be 1 *)
value "fib 3" (* should be 2 *)

thm fib.induct (* rule induction theorem for fib *)

theorem "luc n \<ge> fib n"
  apply (rule fib.induct[of "\<lambda>n. luc n \<ge> fib n"])
  apply (case_tac "n < 2")
  apply auto
  done
  
theorem "luc (n + 1) = fib n + fib (n + 2)"
proof (rule fib.induct[of "\<lambda>n. luc (n + 1) = fib n + fib (n + 2)"])
  fix n
  assume IH1: "n \<noteq> 0 \<Longrightarrow> n \<noteq> 1 \<Longrightarrow> luc (n - 1 + 1) = fib (n - 1) + fib (n - 1 + 2)"
  assume IH2: "n \<noteq> 0 \<Longrightarrow> n \<noteq> 1 \<Longrightarrow> luc (n - 2 + 1) = fib (n - 2) + fib (n - 2 + 2)"

  (* First deal with the easy case where n \<le> 1 *)
  {
    assume "n \<le> 1" (* local assumption *)
    hence "luc (n + 1) = fib n + fib (n + 2)" by simp
  } 
  moreover (* Now deal with the trickier case where n > 1 *)
  {
    assume "n > 1"

    (* Simplify the induction hypotheses *)
    from IH1 have *: "luc n = fib (n - 1) + fib (n + 1)" using `n > 1` by auto
    from IH2 have 
      "luc (n - 2 + 1) = fib (n - 2) + fib (n - 2 + 2)" using `n > 1` by fastforce 
    hence **: "luc (n - 1) = fib (n - 2) + fib n"
      by (metis Nat.add_diff_assoc2 Suc_leI add.commute add_diff_cancel_right' 
          diff_Suc_Suc one_add_one plus_1_eq_Suc `n > 1`)

    (* Some equational reasoning using the definitions of luc and fib to finish the job *)
    have "luc (n + 1) = luc n + luc (n - 1)" using `n > 1` by simp
    also have "... = fib (n - 1) + fib (n + 1) + fib (n - 2) + fib n" using * and ** by simp
    also have "... = fib n + fib (n + 2)" using `n > 1` by simp
    finally have "luc (n + 1) = fib n + fib (n + 2)" by simp
  }
  ultimately show "luc (n + 1) = fib n + fib (n + 2)" by simp
qed

section \<open>Task 4: Balancing circuits.\<close>

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

fun circuits_equiv (infix "\<sim>" 50) (* the "50" indicates the operator precedence *) where
  "c1 \<sim> c2 = (\<forall>\<rho>. simulate c1 \<rho> = simulate c2 \<rho>)"

text \<open>Delay (assuming all gates have a delay of 1)\<close>

fun delay :: "circuit \<Rightarrow> nat" where
  "delay (NOT c) = 1 + delay c"
| "delay (AND c1 c2) = 1 + max (delay c1) (delay c2)"
| "delay (OR c1 c2) = 1 + max (delay c1) (delay c2)" 
| "delay _ = 0"

fun is_balanced where
  "is_balanced (NOT c) = is_balanced c"
| "is_balanced (AND c1 c2) = (is_balanced c1 \<and> is_balanced c2 \<and> delay c1 = delay c2)"
| "is_balanced (OR c1 c2) = (is_balanced c1 \<and> is_balanced c2 \<and> delay c1 = delay c2)"
| "is_balanced _ = True"

value "is_balanced (AND TRUE TRUE)" (* should be True *)
value "is_balanced (AND (NOT TRUE) TRUE)" (* should be False *)
value "is_balanced (AND (NOT TRUE) (OR TRUE (INPUT 1)))" (* should be True *)

(* produce a balanced tree of OR gates whose leaves are all TRUE *)
fun tree_TRUE where
  "tree_TRUE 0 = TRUE"
| "tree_TRUE (Suc n) = OR (tree_TRUE n) (tree_TRUE n)"

value "tree_TRUE 2" (* should be "OR (OR TRUE TRUE) (OR TRUE TRUE)" *)

lemma tree_TRUE_equiv_TRUE:
  "tree_TRUE n \<sim> TRUE"
  by (induct n, auto)

lemma is_balanced_tree_TRUE: "is_balanced (tree_TRUE n)"
  by (induct n, auto)

lemma delay_tree_TRUE: "delay (tree_TRUE n) = n"
  by (induct n, auto)

(* "pad n c" adds a delay of n to circuit c. It does so by AND-ing with TRUE n times. 
  The TRUE is actually produced by a tree of OR-gates of whatever depth is necessary 
  to preserve balance. *)
fun pad where
  "pad 0 c = c"
| "pad (Suc n) c = pad n (AND c (tree_TRUE (delay c)))"

value "pad 2 (INPUT 1)" (* should be "AND (AND (INPUT 1) TRUE) (OR TRUE TRUE)" *)

(* Padding does not change a circuit's behaviour *)
lemma padding_is_sound: 
  "pad n c \<sim> c"
  apply (induct n arbitrary: c)
  using tree_TRUE_equiv_TRUE by auto

(* Padding does not unbalance a circuit *)
lemma padding_preserves_balance: "is_balanced c \<Longrightarrow> is_balanced (pad n c)"
proof (induct n arbitrary: c)
  case 0
  thus "is_balanced (pad 0 c)" by simp
next
  case (Suc n)
  thus "is_balanced (pad (Suc n) c)" 
    using is_balanced_tree_TRUE and delay_tree_TRUE by simp
qed

(* Padding by n adds a delay of n *)
lemma padding_adds_delay: "delay (pad n c) = n + delay c"
  apply (induct n arbitrary: c)
   apply (auto simp add: delay_tree_TRUE)
  done

(* add padding to whichever of c1 and c2 is shorter, then call continuation k *)
fun pad_operands where
  "pad_operands k c1 c2 = (let d1 = delay c1; d2 = delay c2 in 
                       if d1 > d2 then k c1 (pad (d1 - d2) c2) else k (pad (d2 - d1) c1) c2)"

lemma padding_AND_is_sound: 
  "pad_operands AND c1 c2 \<sim> AND c1 c2"
  apply (cases "delay c1 > delay c2")
  using padding_is_sound by auto

lemma padding_OR_is_sound: 
  "pad_operands OR c1 c2 \<sim> OR c1 c2"
  apply (cases "delay c1 > delay c2")
  using padding_is_sound by auto

theorem padding_AND_preserves_balance: 
  "is_balanced c1 \<Longrightarrow> is_balanced c2 \<Longrightarrow> is_balanced (pad_operands AND c1 c2)"
  apply (cases "delay c1 > delay c2")
  apply (auto simp add: padding_adds_delay padding_preserves_balance)
  done

theorem padding_OR_preserves_balance: 
  "is_balanced c1 \<Longrightarrow> is_balanced c2 \<Longrightarrow> is_balanced (pad_operands OR c1 c2)"
  apply (cases "delay c1 > delay c2")
  apply (auto simp add: padding_adds_delay padding_preserves_balance)
  done

fun balance where
  "balance (NOT c) = NOT (balance c)"
| "balance (AND c1 c2) = pad_operands AND (balance c1) (balance c2)"
| "balance (OR c1 c2) = pad_operands OR (balance c1) (balance c2)"
| "balance TRUE = TRUE"
| "balance FALSE = FALSE"
| "balance (INPUT i) = INPUT i"

value "balance (AND TRUE TRUE)" (* unchanged *)
value "balance (AND (NOT TRUE) TRUE)" (* should be AND (NOT TRUE) (OR TRUE TRUE) *)
value "balance (AND TRUE (NOT TRUE))" (* should be AND (OR TRUE TRUE) (NOT TRUE) *)
value "balance (AND (NOT TRUE) (OR TRUE FALSE))" (* unchanged *)

(* balancing a circuit doesn't change its behaviour *)
theorem balance_is_sound: "balance c \<sim> c"
proof (induct c)
  case (AND c1 c2)
  then show ?case using padding_AND_is_sound by auto
next
  case (OR c1 c2)
  then show ?case using padding_OR_is_sound by auto
qed (simp+)

(* balancing a circuit does indeed result in a balanced circuit *)
theorem balance_is_complete: "is_balanced (balance c)"
proof (induct c)
  case (AND c1 c2)
  hence "is_balanced (balance c1)" and "is_balanced (balance c2)" by auto
  hence "is_balanced (pad_operands AND (balance c1) (balance c2))" 
    by (rule padding_AND_preserves_balance)
  thus "is_balanced (balance (AND c1 c2))" by simp
next
  case (OR c1 c2)
  hence "is_balanced (balance c1)" and "is_balanced (balance c2)" by auto
  hence "is_balanced (pad_operands OR (balance c1) (balance c2))" 
    by (rule padding_OR_preserves_balance)
  thus "is_balanced (balance (OR c1 c2))" by simp
qed (simp+)

section \<open>Task 5: Extending with NAND gates.\<close>

datatype "circuit'" = 
  NOT "circuit'"
| AND "circuit'" "circuit'"
| OR "circuit'" "circuit'"
| TRUE
| FALSE
| INPUT "int"
| NAND "circuit'" "circuit'"

fun fake_NOT where
  "fake_NOT c = NAND c TRUE"

fun transform_to_NAND where
  "transform_to_NAND (NOT c) = fake_NOT (transform_to_NAND c)"
| "transform_to_NAND (AND c1 c2) = fake_NOT (NAND (transform_to_NAND c1) (transform_to_NAND c2))"
| "transform_to_NAND (OR c1 c2) = NAND (fake_NOT (transform_to_NAND c1)) (fake_NOT (transform_to_NAND c2))"
| "transform_to_NAND TRUE = TRUE"
| "transform_to_NAND FALSE = fake_NOT TRUE"
| "transform_to_NAND (INPUT i) = INPUT i"
| "transform_to_NAND (NAND c1 c2) = NAND (transform_to_NAND c1) (transform_to_NAND c2)"


text \<open>Simulates a circuit given a valuation for each input wire\<close>

fun simulate' where
  "simulate' (AND c1 c2) \<rho> = ((simulate' c1 \<rho>) \<and> (simulate' c2 \<rho>))"
| "simulate' (OR c1 c2) \<rho> = ((simulate' c1 \<rho>) \<or> (simulate' c2 \<rho>))"
| "simulate' (NOT c) \<rho> = (\<not> (simulate' c \<rho>))"
| "simulate' TRUE \<rho> = True"
| "simulate' FALSE \<rho> = False"
| "simulate' (INPUT i) \<rho> = \<rho> i"
| "simulate' (NAND c1 c2) \<rho> = (\<not> ((simulate' c1 \<rho>) \<and> (simulate' c2 \<rho>)))"

definition circuits_equiv' where
  "circuits_equiv' c1 c2 \<equiv> \<forall>\<rho>. simulate' c1 \<rho> = simulate' c2 \<rho>"

fun only_NANDs :: "circuit' \<Rightarrow> bool" where
  "only_NANDs (AND _ _) = False"
| "only_NANDs (OR _ _) = False"
| "only_NANDs (NOT _) = False"
| "only_NANDs TRUE = True"
| "only_NANDs FALSE = False"
| "only_NANDs (INPUT _) = True"
| "only_NANDs (NAND c1 c2) = (only_NANDs c1 \<and> only_NANDs c2)"

lemma transform_to_NAND_sound: "circuits_equiv' c (transform_to_NAND c)"
  apply (simp add: circuits_equiv'_def)
  apply (induct c)
  apply auto
  done

lemma transform_to_NAND_complete: "only_NANDs (transform_to_NAND c)"
  apply (induct c)
  apply auto
  done

theorem "\<forall>c. \<exists>c'. circuits_equiv' c c' \<and> only_NANDs c'"
  apply clarsimp 
  apply (rule_tac x="transform_to_NAND c" in exI)
  apply (intro conjI)
  apply (simp add: transform_to_NAND_sound)
  apply (simp add: transform_to_NAND_complete)
  done

section \<open>Task 6: Showing that the transformation to NAND gates can increase delay.\<close>

text \<open>Delay (assuming all gates have a delay of 1)\<close>

fun delay' :: "circuit' \<Rightarrow> nat" where
  "delay' (NOT c) = 1 + delay' c"
| "delay' (AND c1 c2) = 1 + max (delay' c1) (delay' c2)"
| "delay' (OR c1 c2) = 1 + max (delay' c1) (delay' c2)"
| "delay' (NAND c1 c2) = 1 + max (delay' c1) (delay' c2)" 
| "delay' _ = 0"

theorem transform_to_NAND_increases_delay: "delay' (transform_to_NAND c) \<le> 2 * delay' c + 1"
  apply (induct c)
  apply auto
  done


end