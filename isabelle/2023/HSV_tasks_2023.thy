theory HSV_tasks_2023 imports Complex_Main begin

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
oops 

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

text \<open> The optimisation is sound: it does not change the circuit's behaviour. \<close>
theorem intro_xor_is_sound: "intro_xor c \<sim> c"
  oops

section \<open> Task 3: A clone function for making lists. \<close>

text \<open> `clone n x` creates a list comprising `n` copies of `x`. \<close>
fun clone :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list"
where
  "clone 0 x = []"
| "clone (Suc n) x = x # clone n x"

value "clone 5 ''Ni''"

lemma rev_clone: "rev (clone n x) = clone n x"
  sorry

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

text \<open> Top-level entry point for the ADC. It zeroes the SAR then calls `adc_helper`. \<close>
definition adc :: "nat \<Rightarrow> real \<Rightarrow> bool list"
where
  "adc w i = adc_helper i ([], clone w False)"

text \<open> Trying out the ADC with various inputs and various bitwidths. \<close>
value "adc 5 9.4"
value "adc 4 9.4"
value "adc 3 9.4"
value "adc 4 5.4"

text \<open> This theorem says that the output of ADC on input i is always less than or equal to i. 
       NB: this is quite a weak theorem, because to capture the behaviour of ADC more fully, 
       we would also want to bound the ADC's output from below. But that property is more 
       complicated because it relies on choosing an appropriate bitwidth, so we'll leave that 
       for another day. \<close>
theorem
  assumes "0 \<le> i"
  shows "real (bits_to_nat (adc w i)) \<le> i"
  oops

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
  oops

end