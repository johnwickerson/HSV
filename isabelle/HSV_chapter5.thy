theory HSV_chapter5 imports Main begin

section \<open>Representing circuits (cf. worksheet Section 5.1)\<close>

text \<open>Defining a data structure to represent fan-out-free circuits with numbered inputs\<close>

datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

text \<open>A few example circuits\<close>

definition "circuit1 == AND (INPUT 1) (INPUT 2)"
definition "circuit2 == OR (NOT circuit1) FALSE"
definition "circuit3 == NOT (NOT circuit2)"
definition "circuit4 == AND circuit3 (INPUT 3)"

section \<open>Simulating circuits (cf. worksheet Section 5.2)\<close>

text \<open>Simulates a circuit given a valuation for each input wire\<close>

fun simulate where
  "simulate (AND c1 c2) \<rho> = ((simulate c1 \<rho>) \<and> (simulate c2 \<rho>))"
| "simulate (OR c1 c2) \<rho> = ((simulate c1 \<rho>) \<or> (simulate c2 \<rho>))"
| "simulate (NOT c) \<rho> = (\<not> (simulate c \<rho>))"
| "simulate TRUE \<rho> = True"
| "simulate FALSE \<rho> = False"
| "simulate (INPUT i) \<rho> = \<rho> i"

text \<open>A few example valuations\<close>

definition "\<rho>0 == \<lambda>_. True"
definition "\<rho>1 == \<rho>0(1 := True, 2 := False, 3 := True)"
definition "\<rho>2 == \<rho>0(1 := True, 2 := True, 3 := True)"

text \<open>Trying out the simulator\<close>

value "simulate circuit1 \<rho>1"
value "simulate circuit2 \<rho>1"
value "simulate circuit3 \<rho>1"
value "simulate circuit4 \<rho>1"
value "simulate circuit1 \<rho>2"
value "simulate circuit2 \<rho>2"
value "simulate circuit3 \<rho>2"
value "simulate circuit4 \<rho>2"

section \<open>Structural induction on circuits (cf. worksheet Section 5.3)\<close>

text \<open>A function that switches each pair of wires entering an OR or AND gate\<close>

fun mirror where
  "mirror (NOT c) = NOT (mirror c)"
| "mirror (AND c1 c2) = AND (mirror c2) (mirror c1)"
| "mirror (OR c1 c2) = OR (mirror c2) (mirror c1)"
| "mirror TRUE = TRUE"
| "mirror FALSE = FALSE"
| "mirror (INPUT i) = INPUT i"

value "circuit1"
value "mirror circuit1"
value "circuit2"
value "mirror circuit2"

text \<open>The following non-theorem is easily contradicted.\<close>

theorem "mirror c = c" 
  oops

text \<open>Proving that mirroring doesn't affect simulation behaviour.\<close>

theorem mirror_is_sound: "simulate (mirror c) \<rho> = simulate c \<rho>"
  by (induct c, auto)

section \<open>A simple circuit optimiser (cf. worksheet Section 5.4)\<close>

text \<open>A function that optimises a circuit by removing pairs of consecutive NOT gates\<close>

fun opt_NOT where
  "opt_NOT (NOT (NOT c)) = opt_NOT c"
| "opt_NOT (NOT c) = NOT (opt_NOT c)"
| "opt_NOT (AND c1 c2) = AND (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT (OR c1 c2) = OR (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT TRUE = TRUE"
| "opt_NOT FALSE = FALSE"
| "opt_NOT (INPUT i) = INPUT i"

text \<open>Trying out the optimiser\<close>

value "circuit1"
value "opt_NOT circuit1"
value "circuit2"
value "opt_NOT circuit2"
value "circuit3"
value "opt_NOT circuit3"
value "circuit4"
value "opt_NOT circuit4"

section \<open>Rule induction (cf. worksheet Section 5.5)\<close>

text \<open>A Fibonacci function that demonstrates complex recursion schemes\<close>

fun f :: "nat \<Rightarrow> nat" where
  "f (Suc (Suc n)) = f n + f (Suc n)"
| "f (Suc 0) = 1"
| "f 0 = 1"

thm f.induct (* rule induction theorem for f *)

text \<open>We need to prove a stronger version of the theorem below
  first, in order to make the inductive step work. Just like how 
  it often goes with loop invariants in Dafny!\<close>
lemma helper: "f n \<ge> n \<and> f n \<ge> 1"
  by (rule f.induct[of "\<lambda>n. f n \<ge> n \<and> f n \<ge> 1"], auto)

text \<open>The nth Fibonacci number is greater than or equal to n\<close>
theorem "f n \<ge> n" 
  using helper by simp

section \<open>Verifying our optimiser (cf. worksheet Section 5.6)\<close>

text \<open>The following non-theorem is easily contradicted.\<close>

theorem "opt_NOT c = c" 
  oops

text \<open>The following theorem says that the optimiser is sound.\<close>

theorem opt_NOT_is_sound: "simulate (opt_NOT c) \<rho> = simulate c \<rho>"
  by (induct rule:opt_NOT.induct, auto)


end
