theory HSV_tasks_2020 imports Complex_Main begin

section \<open>Task 1: proving that "3 / sqrt 2" is irrational.\<close>

(* In case it is helpful, the following theorem is copied from Chapter 3 of the worksheet. *)
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
  sorry (* TODO: Complete this proof. *)

section \<open>Task 2: Centred pentagonal numbers.\<close>

fun pent :: "nat \<Rightarrow> nat" where
  "pent n = (if n = 0 then 1 else 5 * n + pent (n - 1))"

value "pent 0" (* should be 1 *)
value "pent 1" (* should be 6 *)
value "pent 2" (* should be 16 *)
value "pent 3" (* should be 31 *)

theorem "pent n = (5 * n^2 + 5 * n + 2) div 2"
  sorry (* TODO: Complete this proof. *)


section \<open>Task 3: Lucas numbers.\<close>

fun fib :: "nat \<Rightarrow> nat" where
  "fib n = (if n = 0 then 0 else if n = 1 then 1 else fib (n - 1) + fib (n - 2))"

value "fib 0" (* should be 0 *)
value "fib 1" (* should be 1 *)
value "fib 2" (* should be 1 *)
value "fib 3" (* should be 2 *)

thm fib.induct (* rule induction theorem for fib *)

(* TODO: Complete this task. *)


section \<open>Task 4: Balancing circuits.\<close>

(* Here is a datatype for representing circuits, copied from the worksheet *)

datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

text \<open>Delay (assuming all gates have a delay of 1)\<close>

(* The following "delay" function also appeared in the 2019 coursework exercises. *)

fun delay :: "circuit \<Rightarrow> nat" where
  "delay (NOT c) = 1 + delay c"
| "delay (AND c1 c2) = 1 + max (delay c1) (delay c2)"
| "delay (OR c1 c2) = 1 + max (delay c1) (delay c2)" 
| "delay _ = 0"

(* TODO: Complete this task. *)


section \<open>Task 5: Extending with NAND gates.\<close>

(* TODO: Complete this task. *)

end