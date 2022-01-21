theory HSV_tasks_2021_solutions imports Complex_Main begin

section \<open>Task 1: Factorising circuits.\<close>

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
  `(a | b) & (a | c) = a | (b & c)`
  `(a | b) & (c | a) = a | (b & c)`
  `(a | b) & (b | c) = b | (a & c)`
  `(a | b) & (c | b) = b | (a & c)`
 *)
fun factorise where
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

lemma (* test case *)
 "factorise (AND TRUE TRUE) = AND TRUE TRUE"
  by eval
lemma (* test case *)
  "factorise (AND (OR (INPUT 1) FALSE) (OR TRUE (INPUT 1))) = 
  OR (INPUT 1) (AND FALSE TRUE)"
  by eval
lemma (* test case *)
  "factorise (NOT (AND (OR FALSE (INPUT 2)) (OR TRUE (INPUT 2)))) =
  NOT (OR (INPUT 2) (AND FALSE TRUE))"
  by eval

theorem factorise_is_sound: "factorise c \<sim> c"
proof (induct rule: factorise.induct)
  case (2 c1 c2 c3 c4)
  let ?c1' = "factorise c1"
  let ?c2' = "factorise c2"
  let ?c3' = "factorise c3"
  let ?c4' = "factorise c4"
  from 2 have IH: "?c1' \<sim> c1" "?c2' \<sim> c2" "?c3' \<sim> c3" "?c4' \<sim> c4" by auto
  have "factorise (AND (OR c1 c2) (OR c3 c4)) = (
        if ?c1' = ?c3' then OR ?c1' (AND ?c2' ?c4')
        else if ?c1' = ?c4' then OR ?c1' (AND ?c2' ?c3')
        else if ?c2' = ?c3' then OR ?c2' (AND ?c1' ?c4')
        else if ?c2' = ?c4' then OR ?c2' (AND ?c1' ?c3') 
        else AND (OR ?c1' ?c2') (OR ?c3' ?c4'))"
    by auto
  also have "... \<sim> AND (OR c1 c2) (OR c3 c4)" using IH by auto
  finally show ?case by auto
qed(simp_all)

fun factorise2 where
  "factorise2 (NOT c) = NOT (factorise2 c)"
| "factorise2 (AND (OR c1 c2) (OR c3 c4)) = (
    let c1' = factorise2 c1; c2' = factorise2 c2; c3' = factorise2 c3; c4' = factorise2 c4 in
    if c1' = c3' then OR c1' (AND c2' c4') 
    else if c1' = c4' then OR c1' (AND c2' c3') 
    else if c2' = c3' then OR c2' (AND c1' c4') 
    else if c2' = c4' then OR c2' (AND c1' c3') 
    else AND (OR c1' c2') (OR c3' c4'))"
| "factorise2 (OR (AND c1 c2) (AND c3 c4)) = (
    let c1' = factorise2 c1; c2' = factorise2 c2; c3' = factorise2 c3; c4' = factorise2 c4 in
    if c1' = c3' then AND c1' (OR c2' c4') 
    else if c1' = c4' then AND c1' (OR c2' c3') 
    else if c2' = c3' then AND c2' (OR c1' c4') 
    else if c2' = c4' then AND c2' (OR c1' c3') 
    else OR (AND c1' c2') (AND c3' c4'))"
| "factorise2 (AND c1 c2) = AND (factorise2 c1) (factorise2 c2)"
| "factorise2 (OR c1 c2) = OR (factorise2 c1) (factorise2 c2)"
| "factorise2 TRUE = TRUE"
| "factorise2 FALSE = FALSE"
| "factorise2 (INPUT i) = INPUT i"

lemma (* test case *)
  "factorise2 (OR (AND (INPUT 1) (INPUT 2)) (AND TRUE (INPUT 1))) = 
  AND (INPUT 1) (OR (INPUT 2) TRUE)"
  by eval

theorem factorise2_is_sound: "factorise2 c \<sim> c"
proof (induct rule: factorise2.induct)
  case (2 c1 c2 c3 c4)
  let ?c1' = "factorise2 c1"
  let ?c2' = "factorise2 c2"
  let ?c3' = "factorise2 c3"
  let ?c4' = "factorise2 c4"
  from 2 have IH: "?c1' \<sim> c1" "?c2' \<sim> c2" "?c3' \<sim> c3" "?c4' \<sim> c4" by auto
  have "factorise2 (AND (OR c1 c2) (OR c3 c4)) = (
        if ?c1' = ?c3' then OR ?c1' (AND ?c2' ?c4')
        else if ?c1' = ?c4' then OR ?c1' (AND ?c2' ?c3')
        else if ?c2' = ?c3' then OR ?c2' (AND ?c1' ?c4')
        else if ?c2' = ?c4' then OR ?c2' (AND ?c1' ?c3') 
        else AND (OR ?c1' ?c2') (OR ?c3' ?c4'))"
    by auto
  also have "... \<sim> AND (OR c1 c2) (OR c3 c4)" using IH by auto
  finally show ?case by auto
next
  case (3 c1 c2 c3 c4)
  let ?c1' = "factorise2 c1"
  let ?c2' = "factorise2 c2"
  let ?c3' = "factorise2 c3"
  let ?c4' = "factorise2 c4"
  from 3 have IH: "?c1' \<sim> c1" "?c2' \<sim> c2" "?c3' \<sim> c3" "?c4' \<sim> c4" by auto
  have "factorise2 (OR (AND c1 c2) (AND c3 c4)) = (
        if ?c1' = ?c3' then AND ?c1' (OR ?c2' ?c4')
        else if ?c1' = ?c4' then AND ?c1' (OR ?c2' ?c3')
        else if ?c2' = ?c3' then AND ?c2' (OR ?c1' ?c4')
        else if ?c2' = ?c4' then AND ?c2' (OR ?c1' ?c3') 
        else OR (AND ?c1' ?c2') (AND ?c3' ?c4'))"
    by auto
  also have "... \<sim> OR (AND c1 c2) (AND c3 c4)" using IH by auto
  finally show ?case by auto
qed(simp_all)

section \<open>Task 2: A theorem about divisibility.\<close>

theorem plus_dvd_odd_power:
  "(a::int) + b dvd a ^ (2 * n + 1) + b ^ (2 * n + 1)"
proof (induct n)
  case 0 
  thus ?case by auto
next
  case (Suc n)
  then obtain k::int where "a ^ (2 * n + 1) + b ^ (2 * n + 1) = (a + b) * k" 
    unfolding dvd_class.dvd_def by auto
  hence IH: "a ^ (2 * n + 1) = (a + b) * k - b ^ (2 * n + 1)" by auto

  have "a ^ (2 * Suc n + 1) + b ^ (2 * Suc n + 1) = a ^ (2 * n + 2 + 1) + b ^ (2 * n + 2 + 1)"
    by simp
  also have "... = a\<^sup>2 * a ^ (2 * n + 1) + b\<^sup>2 * b ^ (2 * n + 1)"
    by (metis (no_types, lifting) add.commute add_Suc_right plus_1_eq_Suc power_add)
  also have "... = a\<^sup>2 * ((a + b) * k - b ^ (2 * n + 1)) + b\<^sup>2 * b ^ (2 * n + 1)" 
    unfolding IH by auto
  also have "... = a\<^sup>2 * (a + b) * k - a\<^sup>2 * b ^ (2 * n + 1) + b\<^sup>2 * b ^ (2 * n + 1)"
    by algebra
  also have "... = a\<^sup>2 * (a + b) * k - ((a\<^sup>2 - b\<^sup>2) * b ^ (2 * n + 1))"
    by algebra
  also have "... = a\<^sup>2 * (a + b) * k - ((a + b) * (a - b) * b ^ (2 * n + 1))"
    by algebra
  also have "... = (a + b) * (a\<^sup>2 * k - ((a - b) * b ^ (2 * n + 1)))"
    by algebra
  finally have "a ^ (2 * Suc n + 1) + b ^ (2 * Suc n + 1) = 
    (a + b) * (a ^ 2 * k - ((a - b) * b ^ (2 * n + 1)))" .
  thus ?case by simp
qed

theorem plus_dvd_power:
  "(a::int) + b dvd a ^ (2 * n + 2) + b ^ (2 * n + 2)"
  oops

section \<open>Task 3: Proving that the shift-and-add-3 algorithm is correct.\<close>

subsection \<open>Binary and its conversion to nat\<close>

type_synonym bit = "bool"

abbreviation B0 where "B0 == False"
abbreviation B1 where "B1 == True"

(* The following lemma says that if I want to prove a property of 
all 5-bit binary numbers, it suffices to just consider all 32 bit patterns. *)
lemma cases_b5:
  fixes v w x y z :: "bit"
  assumes "(v, w, x, y, z) = (B0, B0, B0, B0, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B0, B0, B0, B0, B1) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B0, B0, B0, B1, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B0, B0, B0, B1, B1) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B0, B0, B1, B0, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B0, B0, B1, B0, B1) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B0, B0, B1, B1, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B0, B0, B1, B1, B1) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B0, B1, B0, B0, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B0, B1, B0, B0, B1) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B0, B1, B0, B1, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B0, B1, B0, B1, B1) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B0, B1, B1, B0, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B0, B1, B1, B0, B1) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B0, B1, B1, B1, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B0, B1, B1, B1, B1) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B0, B0, B0, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B0, B0, B0, B1) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B0, B0, B1, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B0, B0, B1, B1) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B0, B1, B0, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B0, B1, B0, B1) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B0, B1, B1, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B0, B1, B1, B1) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B1, B0, B0, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B1, B0, B0, B1) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B1, B0, B1, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B1, B0, B1, B1) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B1, B1, B0, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B1, B1, B0, B1) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B1, B1, B1, B0) \<Longrightarrow> P v w x y z"
  assumes "(v, w, x, y, z) = (B1, B1, B1, B1, B1) \<Longrightarrow> P v w x y z"
  shows "P v w x y z"
  using assms
  apply (cases v)
   apply (cases w)
    apply (cases x)
     apply (cases y)
      apply (cases z)
       apply auto[2]
     apply (cases z)
      apply auto[2]
    apply (cases y)
     apply (cases z)
      apply auto[2]
    apply (cases z)
     apply auto[2]
   apply (cases x)
    apply (cases y)
     apply (cases z)
      apply auto[2]
    apply (cases z)
     apply auto[2]
   apply (cases y)
    apply (cases z)
     apply auto[2]
   apply (cases z)
    apply auto[2]
  apply (cases w)
   apply (cases x)
    apply (cases y)
     apply (cases z)
      apply auto[2]
    apply (cases z)
     apply auto[2]
   apply (cases y)
    apply (cases z)
     apply auto[2]
   apply (cases z)
    apply auto[2]
  apply (cases x)
   apply (cases y)
    apply (cases z)
     apply auto[2]
   apply (cases z)
    apply auto[2]
  apply (cases y)
   apply (cases z)
    apply auto[2]
  apply (cases z)
  apply auto[2]
  done

fun binary_to_nat :: "bit list \<Rightarrow> nat"
where
  "binary_to_nat [] = 0"
| "binary_to_nat (b # bs) = (if b then 2 ^ length bs else 0) + binary_to_nat bs"


lemma (* test case *) "binary_to_nat [B0, B1, B0, B1] = 5" by eval
lemma (* test case *) "binary_to_nat [B0, B0, B1, B0, B1] = 5" by eval
lemma (* test case *) "binary_to_nat [B1] = 1" by eval
lemma (* test case *) "binary_to_nat [B0] = 0" by eval

subsection \<open>BCD and its conversion to nat\<close>

type_synonym nibble = "bit * bit * bit * bit"

fun nibble_to_nat :: "nibble \<Rightarrow> nat"
where
  "nibble_to_nat (B0,B0,B0,B0) = 0"
| "nibble_to_nat (B0,B0,B0,B1) = 1"
| "nibble_to_nat (B0,B0,B1,B0) = 2"
| "nibble_to_nat (B0,B0,B1,B1) = 3"
| "nibble_to_nat (B0,B1,B0,B0) = 4"
| "nibble_to_nat (B0,B1,B0,B1) = 5"
| "nibble_to_nat (B0,B1,B1,B0) = 6"
| "nibble_to_nat (B0,B1,B1,B1) = 7"
| "nibble_to_nat (B1,B0,B0,B0) = 8"
| "nibble_to_nat (B1,B0,B0,B1) = 9"
| "nibble_to_nat (B1,B0,B1,B0) = 10"
| "nibble_to_nat (B1,B0,B1,B1) = 11"
| "nibble_to_nat (B1,B1,B0,B0) = 12"
| "nibble_to_nat (B1,B1,B0,B1) = 13"
| "nibble_to_nat (B1,B1,B1,B0) = 14"
| "nibble_to_nat (B1,B1,B1,B1) = 15"

fun bcd_to_nat :: "nibble list \<Rightarrow> nat"
where
  "bcd_to_nat [] = 0"
| "bcd_to_nat (n # ns) = bcd_to_nat ns + nibble_to_nat n * 10 ^ length ns"

lemma (* test case *) "bcd_to_nat [(B0,B1,B1,B0)] = 6" by eval
lemma (* test case *) "bcd_to_nat [(B0,B1,B1,B0),(B1,B0,B0,B1)] = 69" by eval
lemma (* test case *) "bcd_to_nat [(B0,B0,B0,B0),(B1,B0,B0,B1)] = 9" by eval
lemma (* test case *) "bcd_to_nat [(B0,B0,B1,B1),(B0,B0,B0,B0)] = 30" by eval


subsection \<open>Left-shifting BCD numbers\<close>

(*
"Add-three-and-shift"
                                                   bcd_part  bin_part         combined
    ([                   ], [1,0,1,0,1,0,1])              0        85      0 + 85 = 85
\<longrightarrow> ([          (0,0,0,1)], [0,1,0,1,0,1])                1        21   1*64 + 21 = 85
\<longrightarrow> ([          (0,0,1,0)], [1,0,1,0,1])                  2        21   2*32 + 21 = 85
\<longrightarrow> ([          (0,1,0,1)], [0,1,0,1])                    5         5    5*16 + 5 = 85
\<longrightarrow> ([(0,0,0,1),(0,0,0,0)], [1,0,1])                     10         5    10*8 + 5 = 85
\<longrightarrow> ([(0,0,1,0),(0,0,0,1)], [0,1])                       21         1    21*4 + 1 = 85
\<longrightarrow> ([(0,1,0,0),(0,0,1,0)], [1])                         42         1    42*2 + 1 = 85
\<longrightarrow> ([(1,0,0,0),(0,1,0,1)], [])                          85         0      85 + 0 = 85
\<longrightarrow> done
*)

fun shift_helper :: "nibble list \<Rightarrow> bit \<Rightarrow> (bit * nibble list)"
  where
  "shift_helper [] b = (b, [])"
| "shift_helper ((b1, b2, b3, b4) # ns) b = (
    let (c, ns') = shift_helper ns b in 
    (b1, (b2,b3,b4,c) # ns'))"

fun shift :: "nibble list \<Rightarrow> bit \<Rightarrow> nibble list"
where
  "shift ns b = (let (c,ns') = shift_helper ns b in 
                 if c = B1 then (B0,B0,B0,c) # ns' else ns')"

lemma (* test case *)
  "shift [(B0, B1, B0, B1), (B1, B0, B1, B0)] B0
       = [(B1, B0, B1, B1), (B0, B1, B0, B0)]" 
by eval

lemma (* test case *)
  "shift [(B1, B1, B0, B1), (B1, B0, B1, B0)] B0
       = [(B0, B0, B0, B1), (B1, B0, B1, B1), (B0, B1, B0, B0)]" 
by eval

lemma (* test case *)
  "shift [] B1
       = [(B0, B0, B0, B1)]" 
by eval

subsection \<open>Functions for adding 3 to BCD digits\<close>

(* Even though this function is only used on nibbles 0 to 9, I've
   defined it as a total, bijective function so that it is invertible;
   this seems to make the proof easier later on. *)
fun maybe_add3 :: "nibble \<Rightarrow> nibble"
where
  "maybe_add3 (B0,B0,B0,B0) = (B0,B0,B0,B0)" (* 0 \<rightarrow> 0 *)
| "maybe_add3 (B0,B0,B0,B1) = (B0,B0,B0,B1)" (* 1 \<rightarrow> 1 *)
| "maybe_add3 (B0,B0,B1,B0) = (B0,B0,B1,B0)" (* 2 \<rightarrow> 2 *)
| "maybe_add3 (B0,B0,B1,B1) = (B0,B0,B1,B1)" (* 3 \<rightarrow> 3 *)
| "maybe_add3 (B0,B1,B0,B0) = (B0,B1,B0,B0)" (* 4 \<rightarrow> 4 *)
| "maybe_add3 (B0,B1,B0,B1) = (B1,B0,B0,B0)" (* 5 \<rightarrow> 8 *)
| "maybe_add3 (B0,B1,B1,B0) = (B1,B0,B0,B1)" (* 6 \<rightarrow> 9 *)
| "maybe_add3 (B0,B1,B1,B1) = (B1,B0,B1,B0)" (* 7 \<rightarrow> 10 *)
| "maybe_add3 (B1,B0,B0,B0) = (B1,B0,B1,B1)" (* 8 \<rightarrow> 11 *)
| "maybe_add3 (B1,B0,B0,B1) = (B1,B1,B0,B0)" (* 9 \<rightarrow> 12 *)
| "maybe_add3 (B1,B0,B1,B0) = (B1,B1,B0,B1)" (* 10 \<rightarrow> 13 *)
| "maybe_add3 (B1,B0,B1,B1) = (B1,B1,B1,B0)" (* 11 \<rightarrow> 14 *)
| "maybe_add3 (B1,B1,B0,B0) = (B1,B1,B1,B1)" (* 12 \<rightarrow> 15 *)
| "maybe_add3 (B1,B1,B0,B1) = (B0,B1,B0,B1)" (* 13 \<rightarrow> 5 *)
| "maybe_add3 (B1,B1,B1,B0) = (B0,B1,B1,B0)" (* 14 \<rightarrow> 6 *)
| "maybe_add3 (B1,B1,B1,B1) = (B0,B1,B1,B1)" (* 15 \<rightarrow> 7 *)

fun maybe_add3_inv :: "nibble \<Rightarrow> nibble"
(* It's sometimes handy to be able to run the `maybe_add3` function backwards *)
where
  "maybe_add3_inv (B0,B0,B0,B0) = (B0,B0,B0,B0)"
| "maybe_add3_inv (B0,B0,B0,B1) = (B0,B0,B0,B1)"
| "maybe_add3_inv (B0,B0,B1,B0) = (B0,B0,B1,B0)"
| "maybe_add3_inv (B0,B0,B1,B1) = (B0,B0,B1,B1)"
| "maybe_add3_inv (B0,B1,B0,B0) = (B0,B1,B0,B0)"
| "maybe_add3_inv (B1,B0,B0,B0) = (B0,B1,B0,B1)"
| "maybe_add3_inv (B1,B0,B0,B1) = (B0,B1,B1,B0)"
| "maybe_add3_inv (B1,B0,B1,B0) = (B0,B1,B1,B1)"
| "maybe_add3_inv (B1,B0,B1,B1) = (B1,B0,B0,B0)"
| "maybe_add3_inv (B1,B1,B0,B0) = (B1,B0,B0,B1)"
| "maybe_add3_inv (B1,B1,B0,B1) = (B1,B0,B1,B0)"
| "maybe_add3_inv (B1,B1,B1,B0) = (B1,B0,B1,B1)"
| "maybe_add3_inv (B1,B1,B1,B1) = (B1,B1,B0,B0)"
| "maybe_add3_inv (B0,B1,B0,B1) = (B1,B1,B0,B1)"
| "maybe_add3_inv (B0,B1,B1,B0) = (B1,B1,B1,B0)"
| "maybe_add3_inv (B0,B1,B1,B1) = (B1,B1,B1,B1)"

lemma maybe_add3_inv1: 
  "maybe_add3_inv (maybe_add3 n) = n"
by (cases n, metis (full_types) maybe_add3.simps maybe_add3_inv.simps)

lemma maybe_add3_inv2: 
  "maybe_add3 (maybe_add3_inv n) = n"
by (cases n, metis (full_types) maybe_add3.simps maybe_add3_inv.simps)


subsection \<open>Converting binary to BCD\<close>

fun binary_to_bcd_helper :: "nibble list \<Rightarrow> bit list \<Rightarrow> nibble list"
where 
  "binary_to_bcd_helper ns [] = ns"
| "binary_to_bcd_helper ns (b # bs) = binary_to_bcd_helper (shift (map maybe_add3 ns) b) bs"

fun binary_to_bcd :: "bit list \<Rightarrow> nibble list"
where
  "binary_to_bcd bs = binary_to_bcd_helper [] bs"  

lemma (* test case *)
  "binary_to_bcd [B1,B0,B1,B0,B1,B0,B1] = [(B1,B0,B0,B0), (B0,B1,B0,B1)]" 
  by eval

(* more test cases *)
lemma "binary_to_bcd [B1,B1,B1] = [(B0,B1,B1,B1)]" by eval 
lemma "binary_to_bcd [B1,B0,B0,B0,B0,B0,B0,B0] = [(B0,B0,B0,B1),(B0,B0,B1,B0),(B1,B0,B0,B0)]" by eval
lemma "binary_to_bcd [B0,B0,B0,B0,B0,B1] = [(B0,B0,B0,B1)]" by eval
lemma "binary_to_bcd [B1,B1,B0,B0,B0,B0,B0] = [(B1,B0,B0,B1),(B0,B1,B1,B0)]" by eval

subsection \<open>Checking that nibbles correspond to valid BCD digits\<close>

fun valid_nibble :: "nibble \<Rightarrow> bool"
where
  "valid_nibble (B0,B0,B0,B0) = True"
| "valid_nibble (B0,B0,B0,B1) = True"
| "valid_nibble (B0,B0,B1,B0) = True"
| "valid_nibble (B0,B0,B1,B1) = True"
| "valid_nibble (B0,B1,B0,B0) = True"
| "valid_nibble (B0,B1,B0,B1) = True"
| "valid_nibble (B0,B1,B1,B0) = True"
| "valid_nibble (B0,B1,B1,B1) = True"
| "valid_nibble (B1,B0,B0,B0) = True"
| "valid_nibble (B1,B0,B0,B1) = True"
| "valid_nibble (B1,B0,B1,B0) = False"
| "valid_nibble (B1,B0,B1,B1) = False"
| "valid_nibble (B1,B1,B0,B0) = False"
| "valid_nibble (B1,B1,B0,B1) = False"
| "valid_nibble (B1,B1,B1,B0) = False"
| "valid_nibble (B1,B1,B1,B1) = False"

lemma shift_helper_valid:
  "list_all valid_nibble ns \<Longrightarrow> 
  list_all valid_nibble (snd (shift_helper (map maybe_add3 ns) b))"
proof (induct ns)
  case Nil
  thus ?case by simp
next
  case (Cons n ns)
  thus ?case
    apply auto
    apply (cases "maybe_add3 n")
    apply auto
    apply (split prod.split)
    apply auto
    apply (cases n)
    apply (smt (z3) maybe_add3.simps valid_nibble.simps prod.inject)
    done
qed

lemma binary_to_bcd_helper_step_valid:
  assumes "list_all valid_nibble ns"
  shows "list_all valid_nibble (shift (map maybe_add3 ns) b)"
using assms
apply auto
apply (split prod.split)
apply (smt (z3) list_all_simps(1) shift_helper_valid snd_conv valid_nibble.simps(2))
done

lemma binary_to_bcd_helper_valid:
  "list_all valid_nibble ns \<Longrightarrow> 
  list_all valid_nibble (binary_to_bcd_helper ns bs)"
proof (induct bs arbitrary: ns)
  case Nil
  thus ?case by auto
next
  case (Cons b bs)
  thus ?case using binary_to_bcd_helper_step_valid by auto
qed

theorem binary_to_bcd_valid:
  "list_all valid_nibble (binary_to_bcd bs)"
using binary_to_bcd_helper_valid by auto
  
subsection \<open>Proof that the binary_to_bcd translation is correct.\<close>

(* `shift_helper` doesn't change the length of its list *)
lemma length_shift_helper:
  "length ns = length (snd (shift_helper ns b))"
proof (induct ns)
  case Nil
  thus ?case by auto
next
  case (Cons a ns)
  show ?case   
    apply auto
    apply (cases a)
    apply auto
    apply (cases "shift_helper ns b")
    apply (auto simp add: Cons)
    done
qed

lemma shift_helper:
  "list_all valid_nibble ns \<Longrightarrow> 
  shift_helper (map maybe_add3 ns) b = (c, ns') \<Longrightarrow>
  bcd_to_nat ((B0,B0,B0,c) # ns') = bcd_to_nat ns * 2 + (if b then 1 else 0)"
proof (induct ns arbitrary: c ns')
  case Nil
  thus ?case by simp
next
  case (Cons n ns)

  obtain c' ns'' where *: "shift_helper (map maybe_add3 ns) b = (c', ns'')" by fastforce
  with Cons have IH: 
    "bcd_to_nat ((B0, B0, B0, c') # ns'') = bcd_to_nat ns * 2 + (if b then 1 else 0)" by simp

  obtain b1 b2 b3 b4 where maybe_add3_n: "maybe_add3 n = (b1, b2, b3, b4)" 
    by (cases rule: prod_cases4) 
  hence "maybe_add3_inv (maybe_add3 n) = maybe_add3_inv (b1, b2, b3, b4)" by auto
  with maybe_add3_inv1 have n_def: "n = maybe_add3_inv (b1, b2, b3, b4)" by auto

  have "c = b1" and ns'_def: "ns' = (b2, b3, b4, c') # ns''" using maybe_add3_n * Cons by auto

  have "length ns'' = length ns" 
    by (metis * length_map length_shift_helper snd_conv)

  have "nibble_to_nat (b2, b3, b4, c') * 10 ^ length ns +
    nibble_to_nat (B0, B0, B0, b1) * 10 * 10 ^ length ns =
    nibble_to_nat (B0, B0, B0, c') * 10 ^ length ns + 
    nibble_to_nat n * 10 ^ length ns * 2"
    apply (rule cases_b5[of b1 b2 b3 b4 c'])
    using Cons apply (auto simp add: n_def)
    done
  thus ?case using ns'_def IH `length ns'' = length ns` `c = b1` by auto
qed

(* Determines the "current state" of a translation-in-progress. See examples below. *)
fun bcd_binary_to_nat :: "nibble list \<Rightarrow> bit list \<Rightarrow> nat"
where
  "bcd_binary_to_nat ns bs = bcd_to_nat ns * 2 ^ length bs + binary_to_nat bs"

lemma "bcd_binary_to_nat                             [] [B1,B0,B1,B0,B1,B0,B1] = 85" by eval
lemma "bcd_binary_to_nat                [(B0,B0,B0,B1)] [B0,B1,B0,B1,B0,B1]    = 85" by eval
lemma "bcd_binary_to_nat                [(B0,B0,B1,B0)] [B1,B0,B1,B0,B1]       = 85" by eval
lemma "bcd_binary_to_nat                [(B0,B1,B0,B1)] [B0,B1,B0,B1]          = 85" by eval
lemma "bcd_binary_to_nat [(B0,B0,B0,B1), (B0,B0,B0,B0)] [B1,B0,B1]             = 85" by eval
lemma "bcd_binary_to_nat [(B0,B0,B1,B0), (B0,B0,B0,B1)] [B0,B1]                = 85" by eval
lemma "bcd_binary_to_nat [(B0,B1,B0,B0), (B0,B0,B1,B0)] [B1]                   = 85" by eval
lemma "bcd_binary_to_nat [(B1,B0,B0,B0), (B0,B1,B0,B1)] []                     = 85" by eval

lemma binary_to_bcd_helper_step_correct:
  assumes "list_all valid_nibble ns"
  shows "bcd_binary_to_nat ns (b # bs) =
         bcd_binary_to_nat (shift (map maybe_add3 ns) b) bs"
proof -
  have "bcd_to_nat (shift (map maybe_add3 ns) B0) = bcd_to_nat ns * 2"
    apply (auto simp del: bcd_to_nat.simps)
    apply (split prod.split)
    apply (auto simp del: bcd_to_nat.simps)
    using assms shift_helper apply presburger
    apply (smt (z3) assms shift_helper add.right_neutral bcd_to_nat.simps(2)
     mult_zero_left nibble_to_nat.simps(1))
    done
  moreover
  have "bcd_to_nat (shift (map maybe_add3 ns) B1) = bcd_to_nat ns * 2 + 1"
    apply (auto simp del: bcd_to_nat.simps)
    apply (split prod.split)
    apply (auto simp del: bcd_to_nat.simps)
     using assms shift_helper apply presburger
    apply (smt (z3) One_nat_def add_Suc_shift add_right_imp_eq assms bcd_to_nat.simps(2) 
       mult_zero_left nibble_to_nat.simps(1) shift_helper)
    done
  ultimately show ?thesis using assms by auto
qed

lemma binary_to_bcd_helper_correct:
  "list_all valid_nibble ns \<Longrightarrow> 
  bcd_to_nat (binary_to_bcd_helper ns bs) = bcd_binary_to_nat ns bs"
proof (induct bs arbitrary: ns)
  case Nil
  thus ?case by simp
next
  case Cons
  thus ?case 
    using binary_to_bcd_helper_step_correct and binary_to_bcd_helper_step_valid 
    by auto
qed

theorem binary_to_bcd_correct:
  "bcd_to_nat (binary_to_bcd bs) = binary_to_nat bs"
using binary_to_bcd_helper_correct by auto

section \<open> Alternative implementation of binary_to_bcd that converts to nat and then to bcd \<close>

lemma mod10_induct [case_names 0 1 2 3 4 5 6 7 8 9]:
  fixes n :: nat
  assumes "P 0" "P 1" "P 2" "P 3" "P 4" "P 5" "P 6" "P 7" "P 8" "P 9"
  shows "P (n mod 10)"
proof -
  have "n mod 10 \<in> {..<10}"
    by simp
  also have "{..<10} = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9 :: nat}"
    by (simp add: lessThan_nat_numeral lessThan_Suc insert_commute)
  finally show ?thesis using assms
    by fastforce
qed
  
fun nat_to_nibble :: "nat \<Rightarrow> nibble"
where
  "nat_to_nibble n = (
     if n = 0 then (B0,B0,B0,B0) else
     if n = 1 then (B0,B0,B0,B1) else
     if n = 2 then (B0,B0,B1,B0) else
     if n = 3 then (B0,B0,B1,B1) else
     if n = 4 then (B0,B1,B0,B0) else
     if n = 5 then (B0,B1,B0,B1) else
     if n = 6 then (B0,B1,B1,B0) else
     if n = 7 then (B0,B1,B1,B1) else
     if n = 8 then (B1,B0,B0,B0) else
     if n = 9 then (B1,B0,B0,B1) else 
                   (B1,B1,B1,B1))" (* unreachable *)

fun nat_to_bcd :: "nat \<Rightarrow> nibble list"
where
  "nat_to_bcd n = (if n = 0 then [] else
     nat_to_bcd (n div 10) @ [nat_to_nibble (n mod 10)])"

value "nat_to_bcd 420"
value "nat_to_bcd 42"
value "nat_to_bcd 4"
value "nat_to_bcd 0"

fun binary_to_bcd2 :: "bit list \<Rightarrow> nibble list"
where
  "binary_to_bcd2 bs = nat_to_bcd (binary_to_nat bs)" 

lemma nat_to_nibble_valid:
  "valid_nibble (nat_to_nibble (n mod 10))"
by (induct rule: mod10_induct, auto)

lemma nat_to_bcd_valid:
  "list_all valid_nibble (nat_to_bcd n)"
  using nat_to_nibble_valid 
  by (induct rule: nat_to_bcd.induct, simp)

theorem binary_to_bcd2_valid:
 "list_all valid_nibble (binary_to_bcd2 bs)"
using nat_to_bcd_valid by auto

lemma bcd_to_nat_snoc:
  "bcd_to_nat (ns @ [n]) = bcd_to_nat ns * 10 + bcd_to_nat [n]"
  by (induct ns, auto)

lemma bcd_to_nat_nibble:
  "bcd_to_nat [nat_to_nibble (n mod 10)] = n mod 10"
  by (induct rule: mod10_induct, auto)

lemma bcd_to_nat_inv:
  "bcd_to_nat (nat_to_bcd n) = n"
  apply (induct rule: nat_to_bcd.induct)
  apply (subst nat_to_bcd.simps)
  apply (case_tac "n=0")
   apply simp
  apply (simp del: nat_to_bcd.simps nat_to_nibble.simps)
  apply (subst bcd_to_nat_snoc)
  apply (subst bcd_to_nat_nibble)
  apply simp
  done

theorem binary_to_bcd2_correct:
  "bcd_to_nat (binary_to_bcd2 bs) = binary_to_nat bs"
  using bcd_to_nat_inv by auto

end