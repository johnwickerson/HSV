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

fun fib :: "nat \<Rightarrow> nat" where
  "fib (Suc (Suc n)) = fib n + fib (Suc n)"
| "fib (Suc 0) = 1"
| "fib 0 = 1"

thm fib.induct (* rule induction theorem for fib *)

text \<open>The nth Fibonacci number is greater than or equal to n\<close>
theorem "fib n \<ge> n" 
proof (induct rule: fib.induct[of "\<lambda>n. fib n \<ge> n"])
  case (1 n)
  thus ?case 
    by (metis One_nat_def add_mono_thms_linordered_semiring(1) fib.simps(1) 
              fib.simps(3) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
qed (auto)

section \<open>Proving termination (cf. worksheet Section 5.6)\<close>

fun \<theta> :: "nat \<Rightarrow> nat" where
  "\<theta> n = 3 - ((n + 3) mod 4)"

value "[\<theta> 0, \<theta> 1, \<theta> 2, \<theta> 3, \<theta> 4, \<theta> 5, \<theta> 6, \<theta> 7, \<theta> 8]"

function g :: "nat \<Rightarrow> nat" where
  "g n = (if n mod 4 = 0 then n else g (n + 1))"
  by pat_completeness auto
termination by (relation "measure \<theta>") (auto, presburger)



section \<open>Verifying our optimiser (cf. worksheet Section 5.7)\<close>

text \<open>The following non-theorem is easily contradicted.\<close>

theorem "opt_NOT c = c" 
  oops

text \<open>The following theorem says that the optimiser is sound.\<close>

theorem opt_NOT_is_sound: "simulate (opt_NOT c) \<rho> = simulate c \<rho>"
  by (induct rule:opt_NOT.induct, auto)


end
