theory HSV_tasks_2023_solutions imports Complex_Main begin

section \<open> Task 1: Extending our circuit synthesiser to handle XOR gates. \<close>

text \<open> Datatype for representing simple circuits, extended with XOR gates. \<close>
datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| XOR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

text \<open> Simulates a circuit given a valuation for each input wire. \<close>
fun simulate where
  "simulate (AND c1 c2) \<rho> = ((simulate c1 \<rho>) \<and> (simulate c2 \<rho>))"
| "simulate (OR c1 c2) \<rho> = ((simulate c1 \<rho>) \<or> (simulate c2 \<rho>))"
| "simulate (XOR c1 c2) \<rho> = ((simulate c1 \<rho>) \<noteq> (simulate c2 \<rho>))"
| "simulate (NOT c) \<rho> = (\<not> (simulate c \<rho>))"
| "simulate TRUE \<rho> = True"
| "simulate FALSE \<rho> = False"
| "simulate (INPUT i) \<rho> = \<rho> i"

text \<open> Equivalence between circuits. \<close>
fun circuits_equiv (infix "\<sim>" 50) (* the "50" indicates the operator precedence *) where
  "c1 \<sim> c2 = (\<forall>\<rho>. simulate c1 \<rho> = simulate c2 \<rho>)"

text \<open> Declaring a "trans" lemma allows `\<sim>` to appear in calculation chains. \<close>
lemma[trans]: "\<lbrakk> c1 \<sim> c2; c2 \<sim> c3 \<rbrakk> \<Longrightarrow> c1 \<sim> c3" by simp

text \<open> This is an optimisation that removes XOR gates from a given circuit. It exploits 
       the following Boolean identity:

            a xor b = (a \<or> b) \<and> \<not>(a \<and> b)
     \<close>
fun elim_xor where
  "elim_xor (AND c1 c2) = 
         AND (elim_xor c1) (elim_xor c2)"
| "elim_xor (OR c1 c2) = 
         OR (elim_xor c1) (elim_xor c2)"
| "elim_xor (XOR c1 c2) = (
         let c1 = elim_xor c1; c2 = elim_xor c2 in 
         AND (OR c1 c2) (NOT (AND c1 c2)))"
| "elim_xor (NOT c) = NOT (elim_xor c)"
| "elim_xor TRUE = TRUE"
| "elim_xor FALSE = FALSE"
| "elim_xor (INPUT i) = INPUT i"

text \<open> An example of the optimisation in action. \<close>
value "elim_xor (XOR (XOR (INPUT 1) (INPUT 2)) (XOR (INPUT 3) (INPUT 4)))"

text \<open> The optimisation is sound: it does not change the circuit's behaviour. \<close>
theorem elim_xor_is_sound: "elim_xor c \<sim> c"
proof (induct c)
  case (XOR c1 c2) (* the only case that cannot be handled by `simp` is the XOR case *)
  let ?c1' = "elim_xor c1"
  let ?c2' = "elim_xor c2"

  have "elim_xor (XOR c1 c2) 
                 = AND (OR ?c1' ?c2') (NOT (AND ?c1' ?c2'))"
    by (meson elim_xor.simps(3))
  also have "... \<sim> AND (OR c1 c2) (NOT (AND c1 c2))" using XOR by simp
  also have "... \<sim> XOR c1 c2" by auto
  finally show ?case by blast
qed (simp+)

section \<open> Task 2: An optimisation that introduces XOR gates. \<close>

text \<open> This is an optimisation that seeks to introduce XOR gates into a given circuit. 
       It exploits the following Boolean identities:
     
            (a \<or> b) \<and> \<not>(a \<and> b) = a xor b
            (b \<or> a) \<and> \<not>(a \<and> b) = a xor b
            (a \<or> b) \<and> \<not>(b \<and> a) = a xor b
            (b \<or> a) \<and> \<not>(b \<and> a) = a xor b
            \<not>(a \<and> b) \<and> (a \<or> b) = a xor b
            \<not>(a \<and> b) \<and> (b \<or> a) = a xor b
            \<not>(b \<and> a) \<and> (a \<or> b) = a xor b
            \<not>(b \<and> a) \<and> (b \<or> a) = a xor b
     \<close>
fun intro_xor where
  "intro_xor (AND (OR a b) (NOT (AND c d))) = (
   let a = intro_xor a; b = intro_xor b; 
       c = intro_xor c; d = intro_xor d in
   if a=c \<and> b=d \<or> a=d \<and> b=c then XOR a b else 
   (AND (OR a b) (NOT (AND c d))))"
| "intro_xor (AND (NOT (AND a b)) (OR c d)) = (
   let a = intro_xor a; b = intro_xor b; 
       c = intro_xor c; d = intro_xor d in
   if a=c \<and> b=d \<or> a=d \<and> b=c then XOR a b else 
   (AND (NOT (AND a b)) (OR c d)))"
| "intro_xor (NOT c) = NOT (intro_xor c)"
| "intro_xor (AND c1 c2) = 
           AND (intro_xor c1) (intro_xor c2)"
| "intro_xor (OR c1 c2) = 
           OR (intro_xor c1) (intro_xor c2)"
| "intro_xor (XOR c1 c2) = 
           XOR (intro_xor c1) (intro_xor c2)"
| "intro_xor TRUE = TRUE"
| "intro_xor FALSE = FALSE"
| "intro_xor (INPUT i) = INPUT i"

value "intro_xor (AND (OR (INPUT 1) (INPUT 2)) (NOT (AND (INPUT 2) (INPUT 1))))"

text \<open> Renaming the case names in the theorem used for rule induction on intro_xor. \<close>
lemmas intro_xor_induct = intro_xor.induct[case_names
  AND_OR_NOT_AND AND_NOT_AND_OR]

text \<open> The optimisation is sound: it does not change the circuit's behaviour. \<close>
theorem intro_xor_is_sound: "intro_xor c \<sim> c"
proof (induct rule: intro_xor_induct)
  case (AND_OR_NOT_AND a b c d)
  let ?a' = "intro_xor a"
  let ?b' = "intro_xor b"
  let ?c' = "intro_xor c"
  let ?d' = "intro_xor d"
  from AND_OR_NOT_AND have "?a' \<sim> a" "?b' \<sim> b" "?c' \<sim> c" "?d' \<sim> d" by simp+

  have "intro_xor (AND (OR a b) (NOT (AND c d))) 
       = (if ?a' = ?c' \<and> ?b' = ?d' \<or> ?a' = ?d' \<and> ?b' = ?c' 
          then XOR ?a' ?b' else AND (OR ?a' ?b') (NOT (AND ?c' ?d')))" by auto
  also have "... \<sim> (AND (OR ?a' ?b') (NOT (AND ?c' ?d')))" 
    by (case_tac "?a' = ?c' \<and> ?b' = ?d' \<or> ?a' = ?d' \<and> ?b' = ?c'", auto)
  also have "... \<sim> (AND (OR a b) (NOT (AND c d)))"
    using AND_OR_NOT_AND by simp 
  finally show ?case by blast
next
  case (AND_NOT_AND_OR a b c d)
  let ?a' = "intro_xor a"
  let ?b' = "intro_xor b"
  let ?c' = "intro_xor c"
  let ?d' = "intro_xor d"
  from AND_NOT_AND_OR have "?a' \<sim> a" "?b' \<sim> b" "?c' \<sim> c" "?d' \<sim> d" by simp+

  have "intro_xor (AND (NOT (AND a b)) (OR c d)) 
       = (if ?a' = ?c' \<and> ?b' = ?d' \<or> ?a' = ?d' \<and> ?b' = ?c' 
          then XOR ?a' ?b' else (AND (NOT (AND ?a' ?b')) (OR ?c' ?d')))" by auto
  also have "... \<sim> (AND (NOT (AND ?a' ?b')) (OR ?c' ?d'))" 
    by (case_tac "?a' = ?c' \<and> ?b' = ?d' \<or> ?a' = ?d' \<and> ?b' = ?c'", auto)
  also have "... \<sim> (AND (NOT (AND a b)) (OR c d))" 
    using AND_NOT_AND_OR by simp
  finally show ?case by blast
qed(simp+)

section \<open> Task 3: A clone function for making lists. \<close>

text \<open> `clone n x` creates a list comprising `n` copies of `x`. \<close>
fun clone :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list"
where
  "clone 0 x = []"
| "clone (Suc n) x = x # clone n x"

value "clone 5 ''Ni''"

lemma append_clone:
  "clone (n1+n2) x = clone n1 x @ clone n2 x"
by (induct n1, auto)

lemma rev_clone:
  "rev (clone n x) = clone n x"
  apply (induct n)
   apply simp
  apply (metis One_nat_def Suc_eq_plus1 append_clone clone.simps rev.simps(2))
  done

section \<open> Task 4: Analogue-to-digital conversion. \<close>

text \<open> Interprets a list of booleans as a binary number written _backwards_ (LSB first).  \<close>
fun backward_bits_to_nat :: "bool list \<Rightarrow> nat"
  where
    "backward_bits_to_nat (False # bs) = 2 * backward_bits_to_nat bs"
  | "backward_bits_to_nat (True # bs) = 2 * backward_bits_to_nat bs + 1"
  | "backward_bits_to_nat [] = 0"

text \<open> Interprets a list of booleans as a binary number (written in the normal way, MSB first).  \<close>
definition bits_to_nat :: "bool list \<Rightarrow> nat"
where
  "bits_to_nat bs = backward_bits_to_nat (rev bs)"

text \<open> A list of 0s of any length is always interpreted as 0. \<close>
lemma zeroes_to_nat_is_zero:
  "bits_to_nat (clone w False) = 0"
proof -
  have "bits_to_nat (clone w False) 
                 = backward_bits_to_nat (clone w False)" 
    by (simp add: rev_clone bits_to_nat_def)
  also have "... = 0" by (induct w, auto)
  finally show ?thesis by blast
qed

type_synonym sar = "bool list * bool list"

text \<open> This function performs one step of the ADC. The SAR is represented using two lists, 
       (r1, r2), with r1 representing the first part of the SAR and r2 representing 
       the second part. As the ADC progresses, r1 grows and r2 shrinks. \<close>
fun adc_step :: "real \<Rightarrow> sar \<Rightarrow> sar"
where
  "adc_step i (r1, r2) = (
    let r = r1 @ (True # tl r2) in
    let cmp = real (bits_to_nat r) \<le> i in
    (r1 @ [cmp], tl r2))"

text \<open> A worked example stepping through the ADC process. \<close>
lemma "adc_step 9.4 ([], [False, False, False, False]) = ([True],  [False, False, False])" by eval
lemma "adc_step 9.4 ([True],    [False, False, False]) = ([True, False],  [False, False])" by eval
lemma "adc_step 9.4 ([True, False],    [False, False]) = ([True, False, False],  [False])" by eval
lemma "adc_step 9.4 ([True, False, False],    [False]) = ([True, False, False, True], [])" by eval

text \<open> This function keeps calling `adc_step` until all bits have been processed. \<close>
fun adc_helper :: "real \<Rightarrow> sar \<Rightarrow> bool list"
where
  "adc_helper i (r1, []) = r1"
| "adc_helper i (r1, r2) = adc_helper i (adc_step i (r1, r2))"

text \<open> Picking nicer names for the cases in the rule induction theorem for `adc_helper`. \<close>
lemmas adc_helper_induct = adc_helper.induct[case_names BaseCase InductiveStep]

text \<open> Top-level entry point for the ADC. It zeroes the SAR then calls `adc_helper`. \<close>
definition adc :: "nat \<Rightarrow> real \<Rightarrow> bool list"
where
  "adc w i = adc_helper i ([], clone w False)"

text \<open> Trying out the ADC with various inputs and various bitwidths. \<close>
value "adc 5 9.4"
value "adc 4 9.4"
value "adc 3 9.4"
value "adc 4 5.4"

text \<open> Our strategy for proving `adc` correct is to use rule induction on the `adc_helper` 
       function. Whenever that function produces an output, it must have performed a finite 
       number of recursive calls to get there. So, we should prove that if we do _no_ recursive 
       calls, then the output is correct (base case), and whenever we do _one more_ recursive 
       call, then the output is correct (inductive step). That is, we should come up with a
       property \<phi> such that:
 
       (1)  \<forall>i r1. \<phi> i (r1, []) holds

       (2)  \<forall>i r1 r2. (r2 \<noteq> [] \<longrightarrow> \<phi> i (adc_step i (r1, r2)) \<longrightarrow> \<phi> i (r1, r2)

       Finally we show that if the property holds when we first call `adc_helper`, then the 
       top-level `adc` function is correct. That is:
 
       (3) \<forall>i w. \<phi> i ([], clone w False) \<longrightarrow> adc w i is correct. 
  \<close>
text \<open> We define \<phi> so that it holds iff the `adc_helper` function preserves the `less than 
       or equal to i` property. That is, if the SAR holds a number that is less than or 
       equal to i, then after running `adc_helper` the SAR will still hold a number that is 
       less than or equal to i.
  \<close>

abbreviation bits_to_real where "bits_to_real r \<equiv> real (bits_to_nat r)"

abbreviation \<phi> 
where 
  "\<phi> i r \<equiv> bits_to_real (fst r @ snd r) \<le> i \<longrightarrow> bits_to_real (adc_helper i r) \<le> i"

lemma adc_helper_correct: 
  "\<phi> i r" 
proof (induct rule: adc_helper_induct)
  case (BaseCase i r1)
  thus ?case by auto
next
  case (InductiveStep i r1 b r2)
  thus ?case
    apply auto
    apply (cases "real (bits_to_nat (r1 @ True # r2)) \<le> i")
     apply simp
    apply (metis (full_types))
    done
qed

text \<open> This theorem says that the output of ADC on input i is always less than or equal to i. 
       NB: this is quite a weak theorem, because to capture the behaviour of ADC more fully, 
       we would also want to bound the ADC's output from below. But that property is more 
       complicated because it relies on choosing an appropriate bitwidth, so we'll leave that 
       for another day. \<close>
theorem adc_correct:
  assumes "0 \<le> i"
  shows "bits_to_real (adc w i) \<le> i"
proof -
  have "\<phi> i ([], clone w False)" using adc_helper_correct 
    by blast
  hence "bits_to_real (adc_helper i ([], clone w False)) \<le> i" 
    by (auto simp add: zeroes_to_nat_is_zero assms)
  thus ?thesis using adc_def by presburger
qed

section \<open> Task 5: Fermat's Last Theorem. \<close>

text \<open> This is (a version of) Fermat's right-triangle theorem. (In fact, it is believed to 
       be the only one of his theorems for which his original complete proof survives.) The
       theorem says that if we have an integer-sided right triangle with hypotenuse c and 
       other sides d and e (i.e. d^2 + e^2 = c^2 by Pythagoras), then d and e cannot both 
       be squares (i.e. there do not exist integers a and b such that d = a^2 and e = b^2). 
       It can be stated more concisely as follows: if a, b, and c are all positive integers, 
       then a^4 + b^4 \<noteq> c^2. Without loss of generality, we can assume that
       any such triangle is in a "reduced" form by removing any common factors between a and
       b (i.e. that the GCD of a and b is 1), and we can also assume that a is odd (at least
       one of a and b have to be odd, otherwise they'd have a common factor of 2, so it might 
       as well be a). \<close>

lemma fermat_right_triangle:
  "\<And>a b c::nat. \<lbrakk> a*b*c > 0; odd a; gcd a b = 1 \<rbrakk> \<Longrightarrow> a^4 + b^4 \<noteq> c^2"
  sorry (* You can assume this theorem is true. No need to prove it! *)

text \<open> Your task is to prove Fermat's Last Theorem in the special case where the exponent is 4. 
       The theorem states that if x, y, and z are all positive integers, then x^4 + y^4 is 
       never equal to z^4. You are advised to use the lemma above to help you! \<close>

theorem fermat4: 
  "\<And>x y z::nat. x*y*z > 0 \<Longrightarrow> x^4 + y^4 \<noteq> z^4"
proof (rule ccontr, clarify)
  fix x y z :: "nat"
  assume x4y4z4: "x^4 + y^4 = z^4"
  assume xyz0: "x*y*z > 0"

  define g where "g == gcd x y"

  obtain a where adef: "x = g * a" using gcd_dvd1 g_def by blast
  obtain b where bdef: "y = g * b" using gcd_dvd2 g_def by blast

  have ab_coprime: "gcd a b = 1"
    by (metis adef bdef bot_nat_0.not_eq_extremum 
      coprime_imp_gcd_eq_1 div_gcd_coprime g_def 
      mult_eq_0_iff nonzero_mult_div_cancel_left xyz0)

  have "z^4 = x^4 + y^4" using x4y4z4 by auto 
  also have "... = (g * a)^4 + (g * b)^4" using adef bdef by auto
  also have "... = g^4 * a^4 + g^4 * b^4" by algebra
  also have "... = g^4 * (a^4 + b^4)" by algebra
  finally have z4: "z^4 = g^4 * (a^4 + b^4)" by blast

  hence "g^4 dvd z^4" by simp
  hence gz: "g dvd z" by simp

  have "a^4 + b^4 = z^4 div g^4" using z4 xyz0 by auto
  also have "... = (z div g)^4" by (simp add: gz div_power)
  also have "... = ((z div g)\<^sup>2)\<^sup>2" by simp
  finally have "a^4 + b^4 = ((z div g)\<^sup>2)\<^sup>2" (is "_ = (?c)\<^sup>2") by blast

  hence a4b4c2: "a^4 + b^4 = ?c\<^sup>2" by simp

  have abc0: "a*b*?c > 0" using gz adef bdef xyz0 by auto

  have "odd a \<or> odd b" using ab_coprime by fastforce 
  moreover {
    assume "odd a"
    hence "a ^ 4 + b ^ 4 \<noteq> ?c\<^sup>2"
      using fermat_right_triangle abc0 ab_coprime by presburger
    hence False using a4b4c2 by simp
  } moreover {
    assume "odd b"
    hence "b ^ 4 + a ^ 4 \<noteq> ?c\<^sup>2"
      using fermat_right_triangle abc0 ab_coprime by (metis gcd.commute mult.commute)
    hence False using a4b4c2 by simp
  }
  ultimately show False by blast
qed

end